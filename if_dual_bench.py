#!/usr/bin/env python3
"""Run architecture-aware baseline/dual IF mapping experiments."""

from __future__ import annotations

import argparse
import concurrent.futures
import csv
import os
import re
import shlex
import shutil
import subprocess
import sys
import time
from pathlib import Path


ARCHES = {
    "ultrascale": {"Ksingle": 6, "Idual": 5, "Isharing": 5, "Kdual": 5},
    "versal": {"Ksingle": 6, "Idual": 6, "Isharing": 6, "Kdual": 6},
    "alm": {"Ksingle": 8, "Idual": 8, "Isharing": 4, "Kdual": 6},
}
SINGLE_RE = re.compile(r"\s+lut(?P<n>\d+)\s*#\((?P<tt>[^)]*)\)\s+\S+\s*\(\s*\{(?P<inputs>[^}]*)\}\s*,\s*(?P<out>[^)]+?)\s*\)\s*;")
DUAL_RE = re.compile(r"\s+dual_lut(?P<n>\d+)\s*#\((?P<params>[^)]*)\)\s+\S+\s*\(\s*\{(?P<inputs>[^}]*)\}\s*,\s*(?P<z5>[^,]+?)\s*,\s*(?P<z>[^)]+?)\s*\)\s*;")
CONST_RE = re.compile(r"(?:(?P<bits>\d+)\s*)?'(?P<base>[bBdDhH])(?P<value>[0-9a-fA-F_xzXZ]+)|(?P<plain>[01])")


def split_signals(text: str) -> list[str]:
    return [token.strip() for token in text.split(",") if token.strip()]


def clean_sig(sig: str) -> str:
    sig = sig.strip()
    return sig[1:].strip() if sig.startswith("\\") else sig


def parse_const(sig: str) -> int | None:
    sig = sig.strip()
    m = CONST_RE.fullmatch(sig)
    if not m:
        return None
    if m.group("plain") is not None:
        return int(m.group("plain"))
    value = m.group("value").replace("_", "").lower()
    if "x" in value or "z" in value:
        return None
    return int(value, {"b": 2, "d": 10, "h": 16}[m.group("base").lower()]) & 1


def parse_truth_const(text: str) -> tuple[int, int]:
    text = text.strip()
    m = CONST_RE.fullmatch(text)
    if not m or m.group("plain") is not None:
        raise ValueError(f"expected sized truth-table constant, got {text!r}")
    value = m.group("value").replace("_", "").lower()
    if "x" in value or "z" in value:
        raise ValueError(f"unsupported unknown truth-table constant: {text!r}")
    bits = m.group("bits")
    if bits is not None:
        width = int(bits)
    elif m.group("base").lower() == "b":
        width = len(value)
    elif m.group("base").lower() == "h":
        width = 4 * len(value)
    else:
        width = max(1, int(value, 10).bit_length())
    return int(value, {"b": 2, "d": 10, "h": 16}[m.group("base").lower()]), width


def support_signals(input_terms: list[str], tt: int, width: int) -> list[str]:
    vars_seen: list[str] = []
    term_map: list[tuple[str | None, int | None]] = []
    for term in input_terms:
        const = parse_const(term)
        if const is not None:
            term_map.append((None, const))
        else:
            name = clean_sig(term)
            if name not in vars_seen:
                vars_seen.append(name)
            term_map.append((name, None))

    def eval_with(assign: int, names: list[str]) -> int:
        var_pos = {name: i for i, name in enumerate(names)}
        full_index = 0
        for pos, (name, const) in enumerate(term_map):
            bit = const if const is not None else (assign >> (len(names) - 1 - var_pos[name])) & 1
            if bit:
                full_index |= 1 << (width - 1 - pos)
        return (tt >> full_index) & 1

    support: list[str] = []
    for i_var, name in enumerate(vars_seen):
        bit_pos = len(vars_seen) - 1 - i_var
        for assign in range(1 << len(vars_seen)):
            if (assign >> bit_pos) & 1:
                continue
            if eval_with(assign, vars_seen) != eval_with(assign | (1 << bit_pos), vars_seen):
                support.append(name)
                break
    return support


def dual_terms_and_width(inputs_all: list[str], tt_width: int, n: int) -> tuple[list[str], int]:
    if tt_width == (1 << n):
        return inputs_all, n
    if tt_width == (1 << (n - 1)):
        return inputs_all[1:], n - 1
    raise ValueError(f"dual_lut{n} truth width {tt_width} does not match {1 << n} or {1 << (n - 1)}")


def stats_from_verilog(path: Path, lut_size: int) -> dict[str, int]:
    counts = {f"LUT{i}": 0 for i in range(1, lut_size + 1)}
    dual_count = 0
    physical_pins = 0
    used_input_pins = 0
    deps: dict[str, list[str]] = {}

    for line in path.read_text(errors="ignore").splitlines():
        m_dual = DUAL_RE.match(line)
        if m_dual:
            n = int(m_dual.group("n"))
            params = split_signals(m_dual.group("params"))
            inputs_all = split_signals(m_dual.group("inputs"))
            if len(params) != 2 or len(inputs_all) != n:
                raise ValueError(f"{path}: malformed dual_lut{n}")
            tt0, width0 = parse_truth_const(params[0])
            tt1, width1 = parse_truth_const(params[1])
            if width0 != width1:
                raise ValueError(f"{path}: dual_lut{n} truth widths differ")
            terms, width = dual_terms_and_width(inputs_all, width0, n)
            deps[clean_sig(m_dual.group("z5"))] = support_signals(terms, tt0, width)
            deps[clean_sig(m_dual.group("z"))] = support_signals(terms, tt1, width)
            dual_count += 1
            physical_pins += n + 2
            used_input_pins += len([sig for sig in inputs_all if parse_const(sig) is None]) + 2
            continue

        m_single = SINGLE_RE.match(line)
        if m_single:
            n = int(m_single.group("n"))
            inputs_all = split_signals(m_single.group("inputs"))
            tt, width = parse_truth_const(m_single.group("tt"))
            support = support_signals(inputs_all, tt, width.bit_length() - 1)
            used = max(1, len([sig for sig in inputs_all if parse_const(sig) is None]))
            if used <= lut_size:
                counts[f"LUT{used}"] += 1
            deps[clean_sig(m_single.group("out"))] = support
            physical_pins += used + 1
            used_input_pins += len([sig for sig in inputs_all if parse_const(sig) is None]) + 1

    memo: dict[str, int] = {}

    def depth_of(root: str) -> int:
        root = clean_sig(root)
        if root in memo:
            return memo[root]
        if root not in deps:
            return 0
        memo[root] = 1 + max((depth_of(dep) for dep in deps[root]), default=0)
        return memo[root]

    result = dict(counts)
    result[f"dual_lut{lut_size}"] = dual_count
    result["total_luts"] = sum(counts.values()) + dual_count
    result["max_depth"] = max((depth_of(out) for out in deps), default=0)
    result["physical_pins"] = physical_pins
    result["used_input_pins"] = used_input_pins
    return result


def wait_with_rusage(proc: subprocess.Popen[str]) -> tuple[int, int | None]:
    if hasattr(os, "wait4"):
        pid, status, rusage = os.wait4(proc.pid, 0)
        assert pid == proc.pid
        proc.returncode = os.waitstatus_to_exitcode(status)
        return proc.returncode, rusage.ru_maxrss
    return proc.wait(), None


def run_abc(abc: Path, src: Path, out: Path, lut_size: int, if_opts: str, stream: bool) -> tuple[str, float, int | None]:
    out.parent.mkdir(parents=True, exist_ok=True)
    command = f"read_verilog {shlex.quote(str(src))}; strash; dch; if -K {lut_size} {if_opts}; write_verilog -K {lut_size} {shlex.quote(str(out))}; print_stats"
    argv = [str(abc), "-c", command]
    if shutil.which("stdbuf"):
        argv = ["stdbuf", "-oL", "-eL"] + argv
    start = time.perf_counter()
    proc = subprocess.Popen(argv, cwd=abc.parent, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    assert proc.stdout is not None
    chunks: list[str] = []
    for chunk in proc.stdout:
        chunks.append(chunk)
        if stream:
            sys.stdout.write(chunk)
            sys.stdout.flush()
    retcode, max_rss_kb = wait_with_rusage(proc)
    elapsed = time.perf_counter() - start
    log = "".join(chunks)
    if retcode != 0 or not out.exists():
        raise RuntimeError(f"ABC failed for {src} [{if_opts}]\n{log}")
    return log, elapsed, max_rss_kb


def run_job(abc: Path, bench_dir: Path, out_dir: Path, src: Path, arch: str, mode: str, stream: bool) -> dict[str, str]:
    cfg = ARCHES[arch]
    rel = src.relative_to(bench_dir)
    out = out_dir / arch / mode / f"{rel.with_suffix('')}.v"
    if_opts = "" if mode == "baseline" else f"-P -Q {arch}"
    log, elapsed, max_rss_kb = run_abc(abc.resolve(), src.resolve(), out, cfg["Ksingle"], if_opts, stream)
    log_path = out_dir / arch / mode / f"{rel.with_suffix('')}.log"
    log_path.parent.mkdir(parents=True, exist_ok=True)
    log_path.write_text(log)
    row = {"arch": arch, **{k: str(v) for k, v in cfg.items()}, "design": str(rel), "mode": mode, "verilog": str(out), "runtime_sec": f"{elapsed:.3f}", "max_rss_kb": "" if max_rss_kb is None else str(max_rss_kb)}
    row.update(stats_from_verilog(out, cfg["Ksingle"]))
    return {k: str(v) for k, v in row.items()}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--abc", type=Path, default=Path("./abc"))
    parser.add_argument("--bench-dir", type=Path, default=Path("benchmarks/tested"))
    parser.add_argument("--out-dir", type=Path, default=Path("if_dual_results"))
    parser.add_argument("--jobs", type=int, default=1)
    parser.add_argument("--arch", choices=["ultrascale", "versal", "alm", "all"], default="all")
    args = parser.parse_args()
    arches = list(ARCHES) if args.arch == "all" else [args.arch]
    benches = sorted(args.bench_dir.rglob("*.v"))
    if args.jobs < 1:
        parser.error("--jobs must be at least 1")
    if not benches:
        print(f"no Verilog benchmarks found under {args.bench_dir}")
        return 0

    results: dict[tuple[str, str], dict[str, dict[str, str]]] = {}
    jobs = [(src, arch, mode) for arch in arches for src in benches for mode in ("baseline", "dual")]
    if args.jobs == 1:
        for src, arch, mode in jobs:
            row = run_job(args.abc, args.bench_dir, args.out_dir, src, arch, mode, True)
            results.setdefault((arch, row["design"]), {})[mode] = row
    else:
        print(f"running {len(jobs)} ABC jobs with {args.jobs} workers", flush=True)
        with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as executor:
            futs = {executor.submit(run_job, args.abc, args.bench_dir, args.out_dir, src, arch, mode, False): (src, arch, mode) for src, arch, mode in jobs}
            for fut in concurrent.futures.as_completed(futs):
                row = fut.result()
                results.setdefault((row["arch"], row["design"]), {})[row["mode"]] = row
                print(f"===== {row['arch']} {row['design']} [{row['mode']}] done in {float(row['runtime_sec']):.2f}s =====", flush=True)

    rows: list[dict[str, str]] = []
    runtime_rows: list[dict[str, str]] = []
    for (arch, design), modes in sorted(results.items()):
        baseline = modes.get("baseline")
        base_luts = int(baseline["total_luts"]) if baseline else 0
        base_time = float(baseline["runtime_sec"]) if baseline else 0.0
        for mode in ("baseline", "dual"):
            if mode not in modes:
                continue
            row = modes[mode]
            if mode == "baseline":
                row["area_saved_percent"] = "0.000"
                row["runtime_scale"] = "1.000"
            else:
                row["area_saved_percent"] = f"{100.0 * (base_luts - int(row['total_luts'])) / base_luts:.3f}" if base_luts else ""
                row["runtime_scale"] = f"{float(row['runtime_sec']) / base_time:.3f}" if base_time else ""
            rows.append(row)
        runtime_rows.append({
            "arch": arch,
            "Ksingle": str(ARCHES[arch]["Ksingle"]),
            "Idual": str(ARCHES[arch]["Idual"]),
            "Isharing": str(ARCHES[arch]["Isharing"]),
            "Kdual": str(ARCHES[arch]["Kdual"]),
            "design": design,
            "baseline_sec": modes.get("baseline", {}).get("runtime_sec", "0.000"),
            "baseline_rss_kb": modes.get("baseline", {}).get("max_rss_kb", ""),
            "dual_sec": modes.get("dual", {}).get("runtime_sec", "0.000"),
            "dual_rss_kb": modes.get("dual", {}).get("max_rss_kb", ""),
            "dual_runtime_scale": rows[-1].get("runtime_scale", "") if rows else "",
        })

    max_k = max(ARCHES[a]["Ksingle"] for a in arches)
    fieldnames = ["arch", "Ksingle", "Idual", "Isharing", "Kdual", "design", "mode", "verilog", "runtime_sec", "max_rss_kb"] + [f"LUT{i}" for i in range(1, max_k + 1)] + [f"dual_lut{k}" for k in sorted({ARCHES[a]["Ksingle"] for a in arches})] + ["total_luts", "area_saved_percent", "runtime_scale", "max_depth", "physical_pins", "used_input_pins"]
    args.out_dir.mkdir(parents=True, exist_ok=True)
    with (args.out_dir / "summary.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames, extrasaction="ignore")
        writer.writeheader()
        writer.writerows(rows)
    with (args.out_dir / "runtime_summary.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=["arch", "Ksingle", "Idual", "Isharing", "Kdual", "design", "baseline_sec", "baseline_rss_kb", "dual_sec", "dual_rss_kb", "dual_runtime_scale"])
        writer.writeheader()
        writer.writerows(runtime_rows)
    print(f"wrote {args.out_dir / 'summary.csv'}")
    print(f"wrote {args.out_dir / 'runtime_summary.csv'}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
