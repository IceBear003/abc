#!/usr/bin/env python3
"""Run baseline/strict/dual IF mapping experiments and summarize LUT stats."""

from __future__ import annotations

import argparse
import csv
import shutil
import re
import shlex
import subprocess
import sys
import time
from pathlib import Path


SINGLE_RE = re.compile(r"\s+lut(?P<n>\d+)\s*#\((?P<tt>[^)]*)\)\s+\S+\s*\(\s*\{(?P<inputs>[^}]*)\}\s*,\s*(?P<out>[^)]+?)\s*\)\s*;")
DUAL_RE = re.compile(r"\s+dual_lut(?P<n>\d+)\s*#\((?P<params>[^)]*)\)\s+\S+\s*\(\s*\{(?P<inputs>[^}]*)\}\s*,\s*(?P<z5>[^,]+?)\s*,\s*(?P<z>[^)]+?)\s*\)\s*;")
CONST_RE = re.compile(r"(?:(?P<bits>\d+)\s*)?'(?P<base>[bBdDhH])(?P<value>[0-9a-fA-F_xzXZ]+)|(?P<plain>[01])")


def split_signals(text: str) -> list[str]:
    return [token.strip() for token in text.split(",") if token.strip()]


def is_const(sig: str) -> bool:
    return parse_const(sig) is not None


def clean_sig(sig: str) -> str:
    sig = sig.strip()
    if sig.startswith("\\"):
        sig = sig[1:]
    return sig.strip()


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


def parse_truth_const(text: str) -> int:
    text = text.strip()
    m = CONST_RE.fullmatch(text)
    if not m or m.group("plain") is not None:
        raise ValueError(f"expected sized truth-table constant, got {text!r}")
    value = m.group("value").replace("_", "").lower()
    if "x" in value or "z" in value:
        raise ValueError(f"unsupported unknown truth-table constant: {text!r}")
    return int(value, {"b": 2, "d": 10, "h": 16}[m.group("base").lower()])


def support_signals(input_terms: list[str], tt: int, width: int) -> list[str]:
    """Return only signals that actually affect TT[in].

    This avoids false paths in dual_lutN: z5 ignores the select input, and both
    outputs may ignore padded constants or functionally redundant data inputs.
    """
    vars_seen: list[str] = []
    term_map: list[tuple[str | None, int | None]] = []
    for term in input_terms:
        const = parse_const(term)
        if const is not None:
            term_map.append((None, const))
            continue
        name = clean_sig(term)
        if name not in vars_seen:
            vars_seen.append(name)
        term_map.append((name, None))

    def eval_with(assign: int, names: list[str]) -> int:
        var_pos = {name: i for i, name in enumerate(names)}
        full_index = 0
        for pos, (name, const) in enumerate(term_map):
            if const is not None:
                bit = const
            else:
                bit = (assign >> (len(names) - 1 - var_pos[name])) & 1
            if bit:
                full_index |= 1 << (width - 1 - pos)
        return (tt >> full_index) & 1

    support: list[str] = []
    n_all = len(vars_seen)
    for i_var, name in enumerate(vars_seen):
        depends = False
        bit_pos = n_all - 1 - i_var
        for assign in range(1 << n_all):
            if (assign >> bit_pos) & 1:
                continue
            if eval_with(assign, vars_seen) != eval_with(assign | (1 << bit_pos), vars_seen):
                depends = True
                break
        if depends:
            support.append(name)
    return support


def stats_from_verilog(path: Path, lut_size: int) -> dict[str, int]:
    """Count physical LUT instances and pins from the emitted LUT Verilog.

    Depth is computed from functional support of each emitted LUT output.  This
    is the authoritative dual-output depth because ABC's generic lev statistic
    cannot see that some dual_lut inputs are functionally irrelevant to one of
    the two outputs.
    """
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
            if len(params) != 2:
                raise ValueError(f"{path}: dual_lut{n} expects two truth tables")
            inputs_all = split_signals(m_dual.group("inputs"))
            data_inputs = [clean_sig(sig) for sig in inputs_all if not is_const(sig)]
            z5_terms = inputs_all[1:]
            z5_support = support_signals(z5_terms, parse_truth_const(params[0]), n - 1)
            z_tt = parse_truth_const(params[1])
            z5_tt = parse_truth_const(params[0])
            z_support = support_signals(inputs_all, (z_tt << (1 << (n - 1))) | z5_tt, n)
            deps[clean_sig(m_dual.group("z5"))] = z5_support
            deps[clean_sig(m_dual.group("z"))] = z_support
            dual_count += 1
            # Physical package pins: N shared inputs plus two outputs.  The
            # used-input count ignores padded constants for sanity checking.
            physical_pins += n + 2
            used_input_pins += len(data_inputs) + 2
            continue

        m_single = SINGLE_RE.match(line)
        if m_single:
            n = int(m_single.group("n"))
            inputs_all = split_signals(m_single.group("inputs"))
            data_inputs = [clean_sig(sig) for sig in inputs_all if not is_const(sig)]
            support = support_signals(inputs_all, parse_truth_const(m_single.group("tt")), n)
            used = max(1, len(data_inputs))
            if used <= lut_size:
                counts[f"LUT{used}"] += 1
            deps[clean_sig(m_single.group("out"))] = support
            physical_pins += used + 1
            used_input_pins += len(data_inputs) + 1

    memo: dict[str, int] = {}
    active: set[str] = set()

    def depth_of(root: str) -> int:
        root = clean_sig(root)
        if root not in deps:
            return 0
        stack: list[tuple[str, bool]] = [(root, False)]
        while stack:
            sig, expanded = stack.pop()
            sig = clean_sig(sig)
            if sig not in deps or sig in memo:
                continue
            if expanded:
                active.discard(sig)
                memo[sig] = 1 + max((memo.get(clean_sig(dep), 0) for dep in deps[sig]), default=0)
                continue
            if sig in active:
                memo[sig] = 0
                continue
            active.add(sig)
            stack.append((sig, True))
            for dep in deps[sig]:
                dep = clean_sig(dep)
                if dep in deps and dep not in memo:
                    stack.append((dep, False))
        return memo.get(root, 0)

    max_depth = max((depth_of(out) for out in deps), default=0)
    result = dict(counts)
    result[f"dual_lut{lut_size}"] = dual_count
    result["total_luts"] = sum(counts.values()) + dual_count
    result["max_depth"] = max_depth
    result["physical_pins"] = physical_pins
    result["used_input_pins"] = used_input_pins
    return result


def run_abc(abc: Path, src: Path, out: Path, lut_size: int, if_opts: str) -> tuple[str, float]:
    out.parent.mkdir(parents=True, exist_ok=True)
    # Keep preprocessing identical across modes so the CSV compares only the
    # mapper options: baseline, strict-depth, and dual-output.
    command = (
        f"read_verilog {shlex.quote(str(src))}; "
        "strash; dch; "
        f"if -K {lut_size} {if_opts}; "
        f"write_verilog -K {lut_size} {shlex.quote(str(out))}; "
        "print_stats"
    )
    argv = [str(abc), "-c", command]
    if shutil.which("stdbuf"):
        argv = ["stdbuf", "-oL", "-eL"] + argv
    start = time.perf_counter()
    proc = subprocess.Popen(
        argv,
        cwd=abc.parent,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    chunks: list[str] = []
    assert proc.stdout is not None
    for chunk in proc.stdout:
        chunks.append(chunk)
        sys.stdout.write(chunk)
        sys.stdout.flush()
    retcode = proc.wait()
    elapsed = time.perf_counter() - start
    log = "".join(chunks)
    if retcode != 0 or not out.exists():
        raise RuntimeError(f"ABC failed for {src} [{if_opts}]\n{log}")
    return log, elapsed


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--abc", type=Path, default=Path("./abc"))
    parser.add_argument("--bench-dir", type=Path, default=Path("benchmarks/tested"))
    parser.add_argument("--out-dir", type=Path, default=Path("if_dual_results"))
    parser.add_argument("-K", "--lut-size", type=int, default=6)
    args = parser.parse_args()

    benches = sorted(args.bench_dir.rglob("*.v"))
    if not benches:
        print(f"no Verilog benchmarks found under {args.bench_dir}")
        return 0

    modes = [
        ("baseline", ""),
        # ("strict", "-L"),
        ("dual", "-P"),
    ]
    rows = []
    runtime_rows = []
    for src in benches:
        rel = src.relative_to(args.bench_dir)
        stem = rel.with_suffix("")
        design_start = time.perf_counter()
        mode_times = {}
        design_rows = []
        for mode, if_opts in modes:
            out = args.out_dir / mode / f"{stem}.v"
            print(f"\n===== {rel} [{mode}] start =====", flush=True)
            log, elapsed = run_abc(args.abc.resolve(), src.resolve(), out, args.lut_size, if_opts)
            print(f"===== {rel} [{mode}] done in {elapsed:.2f}s =====\n", flush=True)
            mode_times[mode] = elapsed
            (args.out_dir / mode / f"{stem}.log").parent.mkdir(parents=True, exist_ok=True)
            (args.out_dir / mode / f"{stem}.log").write_text(log)
            row = {"design": str(rel), "mode": mode, "verilog": str(out), "runtime_sec": f"{elapsed:.3f}"}
            row.update(stats_from_verilog(out, args.lut_size))
            design_rows.append(row)
        baseline_row = next((row for row in design_rows if row["mode"] == "baseline"), None)
        baseline_luts = int(baseline_row["total_luts"]) if baseline_row else 0
        baseline_time = mode_times.get("baseline", 0.0)
        for row in design_rows:
            total_luts = int(row["total_luts"])
            runtime = float(row["runtime_sec"])
            if row["mode"] == "baseline":
                row["area_saved_percent"] = "0.000"
                row["runtime_scale"] = "1.000"
            elif baseline_luts > 0:
                row["area_saved_percent"] = f"{100.0 * (baseline_luts - total_luts) / baseline_luts:.3f}"
                row["runtime_scale"] = f"{runtime / baseline_time:.3f}" if baseline_time > 0 else ""
            else:
                row["area_saved_percent"] = ""
                row["runtime_scale"] = ""
            rows.append(row)
        runtime_rows.append({
            "design": str(rel),
            "baseline_sec": f"{mode_times.get('baseline', 0.0):.3f}",
            "strict_sec": f"{mode_times.get('strict', 0.0):.3f}",
            "dual_sec": f"{mode_times.get('dual', 0.0):.3f}",
            "strict_runtime_scale": f"{mode_times.get('strict', 0.0) / mode_times['baseline']:.3f}" if mode_times.get("baseline", 0.0) > 0 else "",
            "dual_runtime_scale": f"{mode_times.get('dual', 0.0) / mode_times['baseline']:.3f}" if mode_times.get("baseline", 0.0) > 0 else "",
            "total_sec": f"{time.perf_counter() - design_start:.3f}",
        })

    fieldnames = ["design", "mode", "verilog", "runtime_sec"] + [f"LUT{i}" for i in range(1, args.lut_size + 1)] + [
        f"dual_lut{args.lut_size}",
        "total_luts",
        "area_saved_percent",
        "runtime_scale",
        "max_depth",
        "physical_pins",
        "used_input_pins",
    ]
    args.out_dir.mkdir(parents=True, exist_ok=True)
    with (args.out_dir / "summary.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)
    with (args.out_dir / "runtime_summary.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=["design", "baseline_sec", "strict_sec", "dual_sec", "strict_runtime_scale", "dual_runtime_scale", "total_sec"])
        writer.writeheader()
        writer.writerows(runtime_rows)
    print(f"wrote {args.out_dir / 'summary.csv'}")
    print(f"wrote {args.out_dir / 'runtime_summary.csv'}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
