#!/usr/bin/env python3
"""Run ABC CEC for original benchmarks against architecture-aware baseline/dual LUT outputs."""

from __future__ import annotations

import argparse
import concurrent.futures
import csv
import re
import shlex
import shutil
import subprocess
import sys
import time
from pathlib import Path


LUT_INST_RE = re.compile(
    r"^\s*lut(?P<n>\d+)\s*#\((?P<tt>[^)]*)\)\s+\S+\s*"
    r"\(\s*\{(?P<inputs>[^}]*)\}\s*,\s*(?P<out>[^)]+?)\s*\)\s*;",
    re.MULTILINE,
)
DUAL_INST_RE = re.compile(
    r"^\s*dual_lut(?P<n>\d+)\s*#\((?P<params>[^)]*)\)\s+\S+\s*"
    r"\(\s*\{(?P<inputs>[^}]*)\}\s*,\s*(?P<z5>[^,]+?)\s*,\s*(?P<z>[^)]+?)\s*\)\s*;",
    re.MULTILINE,
)
MODULE_RE = re.compile(r"\bmodule\s+(?P<name>[A-Za-z_][A-Za-z0-9_$]*)\b(?P<body>.*?)\bendmodule\b", re.DOTALL)
CONST_RE = re.compile(r"(?:(?P<bits>\d+)\s*)?'(?P<base>[bBdDhH])(?P<value>[0-9a-fA-F_xzXZ]+)|(?P<plain>[01])")
CEC_PASS_RE = re.compile(r"Networks are equivalent|Networks are combinationally equivalent", re.IGNORECASE)
CEC_FAIL_RE = re.compile(r"Networks are NOT EQUIVALENT|are not equivalent|not equivalent", re.IGNORECASE)
CEC_READ_ERROR_RE = re.compile(r"Reading network from file has failed|Network contains a combinational loop|NetworkCheck:", re.IGNORECASE)
ARCH_CONFIGS = {
    "ultrascale": {"Ksingle": 6, "Idual": 5, "Isharing": 5, "Kdual": 5},
    "versal": {"Ksingle": 6, "Idual": 6, "Isharing": 6, "Kdual": 6},
    "alm": {"Ksingle": 8, "Idual": 8, "Isharing": 4, "Kdual": 6},
}


def split_csv(text: str) -> list[str]:
    return [token.strip() for token in text.split(",") if token.strip()]


def clean_name(sig: str) -> str:
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
        raise ValueError(f"unsupported unknown constant in LUT input: {sig}")
    base = m.group("base").lower()
    return int(value, {"b": 2, "d": 10, "h": 16}[base]) & 1


def parse_hex_const(text: str) -> int:
    text = text.strip()
    m = CONST_RE.fullmatch(text)
    if not m or m.group("plain") is not None:
        raise ValueError(f"expected sized Verilog constant, got: {text}")
    value = m.group("value").replace("_", "").lower()
    if "x" in value or "z" in value:
        raise ValueError(f"unsupported unknown truth-table constant: {text}")
    base = m.group("base").lower()
    return int(value, {"b": 2, "d": 10, "h": 16}[base])


def truth_const_width(text: str) -> int:
    text = text.strip()
    m = CONST_RE.fullmatch(text)
    if not m or m.group("plain") is not None:
        raise ValueError(f"expected sized Verilog constant, got: {text}")
    bits = m.group("bits")
    if bits is not None:
        return int(bits)
    value = m.group("value").replace("_", "")
    base = m.group("base").lower()
    if base == "b":
        return len(value)
    if base == "h":
        return 4 * len(value)
    return max(1, int(value, 10).bit_length())


def dual_output_specs(src: Path, width: int, params: list[str], terms: list[str], out0: str, out1: str) -> list[tuple[str, list[str], int, int]]:
    if len(params) != 2:
        raise ValueError(f"{src}: dual_lut{width} expects two truth-table parameters")
    if len(terms) != width:
        raise ValueError(f"{src}: dual_lut{width} has {len(terms)} inputs")
    tt0 = parse_hex_const(params[0])
    tt1 = parse_hex_const(params[1])
    bits0 = truth_const_width(params[0])
    bits1 = truth_const_width(params[1])
    if bits0 != bits1:
        raise ValueError(f"{src}: dual_lut{width} mixes truth-table widths {bits0} and {bits1}")
    new_bits = 1 << width
    old_bits = 1 << (width - 1) if width > 0 else 1
    if bits0 == new_bits:
        return [
            (clean_name(out0), terms, tt0, width),
            (clean_name(out1), terms, tt1, width),
        ]
    if width > 0 and bits0 == old_bits:
        legacy_terms = terms[1:]
        return [
            (clean_name(out0), legacy_terms, tt0, width - 1),
            (clean_name(out1), legacy_terms, tt1, width - 1),
        ]
    raise ValueError(
        f"{src}: dual_lut{width} truth tables must have {new_bits} bits (new format) "
        f"or {old_bits} bits (legacy format), got {bits0}"
    )


def find_top_module(text: str) -> tuple[str, str]:
    for m in MODULE_RE.finditer(text):
        name = m.group("name")
        if not name.startswith("lut") and not name.startswith("dual_lut"):
            return name, m.group("body")
    raise ValueError("could not find mapped top module")


def parse_decl_names(body: str, keyword: str) -> list[str]:
    names: list[str] = []
    for m in re.finditer(rf"\b{keyword}\b(?P<decl>.*?);", body, re.DOTALL):
        for token in split_csv(m.group("decl")):
            token = re.sub(r"^\s*\[[^]]+\]\s*", "", token)
            name = clean_name(token)
            if name:
                names.append(name)
    return names


def blif_wrap(kind: str, names: list[str]) -> list[str]:
    if not names:
        return [f".{kind}"]
    lines: list[str] = []
    cur = f".{kind}"
    for name in names:
        piece = f" {name}"
        if len(cur) + len(piece) > 78:
            lines.append(cur + " \\")
            cur = " " + name
        else:
            cur += piece
    lines.append(cur)
    return lines


def truth_rows(input_terms: list[str], tt: int, width: int) -> tuple[list[str], list[str]]:
    vars_seen: list[str] = []
    term_to_var: list[tuple[str | None, int | None]] = []
    for term in input_terms:
        c = parse_const(term)
        if c is not None:
            term_to_var.append((None, c))
            continue
        name = clean_name(term)
        if name not in vars_seen:
            vars_seen.append(name)
        term_to_var.append((name, None))

    def eval_with(assign: int, names: list[str]) -> int:
        var_pos = {name: i for i, name in enumerate(names)}
        full_index = 0
        for pos, (name, const) in enumerate(term_to_var):
            if const is not None:
                bit = const
            elif name in var_pos:
                bit = (assign >> (len(names) - 1 - var_pos[name])) & 1
            else:
                bit = 0
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

    rows: list[str] = []
    n_vars = len(support)
    for assign in range(1 << n_vars):
        if eval_with(assign, support):
            rows.append("".join("1" if (assign >> (n_vars - 1 - i)) & 1 else "0" for i in range(n_vars)) + " 1")
    return support, rows


def emit_names(lines: list[str], inputs: list[str], out: str, rows: list[str]) -> None:
    lines.append(".names " + " ".join(inputs + [clean_name(out)]))
    lines.extend(rows)


def mapped_verilog_to_blif(src: Path, dst: Path) -> None:
    text = src.read_text(errors="ignore")
    top_name, body = find_top_module(text)
    inputs = parse_decl_names(body, "input")
    outputs = parse_decl_names(body, "output")
    lines = [f".model {top_name}"]
    lines.extend(blif_wrap("inputs", inputs))
    lines.extend(blif_wrap("outputs", outputs))

    for m in LUT_INST_RE.finditer(body):
        width = int(m.group("n"))
        terms = split_csv(m.group("inputs"))
        if len(terms) != width:
            raise ValueError(f"{src}: lut{width} has {len(terms)} inputs")
        vars_seen, rows = truth_rows(terms, parse_hex_const(m.group("tt")), width)
        emit_names(lines, vars_seen, m.group("out"), rows)

    for m in DUAL_INST_RE.finditer(body):
        width = int(m.group("n"))
        params = split_csv(m.group("params"))
        terms = split_csv(m.group("inputs"))
        for out_name, out_terms, tt, tt_width in dual_output_specs(src, width, params, terms, m.group("z5"), m.group("z")):
            vars_seen, rows = truth_rows(out_terms, tt, tt_width)
            emit_names(lines, vars_seen, out_name, rows)

    lines.append(".end")
    dst.parent.mkdir(parents=True, exist_ok=True)
    dst.write_text("\n".join(lines) + "\n")


def run_abc(abc: Path, command: str) -> tuple[int, str, float]:
    argv = [str(abc), "-c", command]
    if shutil.which("stdbuf"):
        argv = ["stdbuf", "-oL", "-eL"] + argv
    start = time.perf_counter()
    proc = subprocess.Popen(argv, cwd=abc.parent, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    chunks: list[str] = []
    assert proc.stdout is not None
    for chunk in proc.stdout:
        chunks.append(chunk)
        sys.stdout.write(chunk)
        sys.stdout.flush()
    retcode = proc.wait()
    return retcode, "".join(chunks), time.perf_counter() - start


def run_abc_capture(abc: Path, command: str) -> tuple[int, str, float]:
    argv = [str(abc), "-c", command]
    if shutil.which("stdbuf"):
        argv = ["stdbuf", "-oL", "-eL"] + argv
    start = time.perf_counter()
    proc = subprocess.run(
        argv,
        cwd=abc.parent,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    return proc.returncode, proc.stdout or "", time.perf_counter() - start


def cec_status(retcode: int, log: str) -> str:
    if retcode != 0:
        return "error"
    if CEC_READ_ERROR_RE.search(log):
        return "read_error"
    if CEC_PASS_RE.search(log):
        return "pass"
    if CEC_FAIL_RE.search(log):
        return "fail"
    return "unknown"


def run_case(
    abc: Path,
    mapped_dir: Path,
    out_dir: Path,
    src: Path,
    bench_dir: Path,
    arch: str,
    mode: str,
    stream: bool,
) -> dict[str, str]:
    rel = src.relative_to(bench_dir)
    stem = rel.with_suffix("")
    mapped = mapped_dir / arch / mode / f"{stem}.v"
    if not mapped.exists():
        legacy_mapped = mapped_dir / mode / f"{stem}.v"
        if legacy_mapped.exists():
            mapped = legacy_mapped
    blif = out_dir / "blif" / arch / mode / f"{stem}.blif"
    log_path = out_dir / "logs" / arch / mode / f"{stem}.log"
    row = {
        "design": str(rel),
        "arch": arch,
        "mode": mode,
        "Ksingle": str(ARCH_CONFIGS[arch]["Ksingle"]),
        "Idual": str(ARCH_CONFIGS[arch]["Idual"]),
        "Isharing": str(ARCH_CONFIGS[arch]["Isharing"]),
        "Kdual": str(ARCH_CONFIGS[arch]["Kdual"]),
        "mapped": str(mapped),
        "blif": str(blif),
    }
    if not mapped.exists():
        row.update({"status": "missing", "runtime_sec": "0.000"})
        return row
    try:
        mapped_verilog_to_blif(mapped, blif)
    except Exception as exc:
        row.update({"status": "convert_error", "runtime_sec": "0.000", "message": str(exc)})
        return row
    command = f"cec {shlex.quote(str(src.resolve()))} {shlex.quote(str(blif.resolve()))}"
    if stream:
        retcode, log, elapsed = run_abc(abc.resolve(), command)
    else:
        retcode, log, elapsed = run_abc_capture(abc.resolve(), command)
    log_path.parent.mkdir(parents=True, exist_ok=True)
    log_path.write_text(log)
    row.update({
        "status": cec_status(retcode, log),
        "runtime_sec": f"{elapsed:.3f}",
        "log": str(log_path),
    })
    return row


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--abc", type=Path, default=Path("./abc"))
    parser.add_argument("--bench-dir", type=Path, default=Path("benchmarks/tested"))
    parser.add_argument("--mapped-dir", type=Path, default=Path("if_dual_results"))
    parser.add_argument("--out-dir", type=Path, default=Path("if_dual_cec"))
    parser.add_argument("--jobs", type=int, default=1)
    parser.add_argument("--arch", choices=["ultrascale", "versal", "alm", "all"], default="all")
    parser.add_argument("--mode", choices=["baseline", "strict", "dual"], action="append")
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be at least 1")

    archs = list(ARCH_CONFIGS) if args.arch == "all" else [args.arch]
    modes = args.mode or ["baseline", "dual"]
    benches = sorted(args.bench_dir.rglob("*.v"))
    if not benches:
        print(f"no Verilog benchmarks found under {args.bench_dir}")
        return 1

    rows: list[dict[str, str]] = []
    if args.jobs == 1:
        for src in benches:
            rel = src.relative_to(args.bench_dir)
            for arch in archs:
                for mode in modes:
                    print(f"\n===== CEC {rel} [{arch}/{mode}] start =====", flush=True)
                    row = run_case(args.abc, args.mapped_dir, args.out_dir, src, args.bench_dir, arch, mode, True)
                    rows.append(row)
                    if row["status"] == "missing":
                        print(f"missing mapped Verilog: {row['mapped']}")
                    elif row["status"] == "convert_error":
                        print(f"conversion failed: {row.get('message', '')}")
                    print(f"===== CEC {rel} [{arch}/{mode}] {row['status']} in {float(row['runtime_sec']):.2f}s =====\n", flush=True)
    else:
        jobs = [(src, arch, mode) for src in benches for arch in archs for mode in modes]
        print(f"running {len(jobs)} CEC jobs with {args.jobs} workers", flush=True)
        with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as executor:
            future_to_job = {
                executor.submit(run_case, args.abc, args.mapped_dir, args.out_dir, src, args.bench_dir, arch, mode, False): (src, arch, mode)
                for src, arch, mode in jobs
            }
            for future in concurrent.futures.as_completed(future_to_job):
                src, arch, mode = future_to_job[future]
                rel = src.relative_to(args.bench_dir)
                row = future.result()
                rows.append(row)
                print(f"===== CEC {rel} [{arch}/{mode}] {row['status']} in {float(row['runtime_sec']):.2f}s =====", flush=True)

    args.out_dir.mkdir(parents=True, exist_ok=True)
    summary = args.out_dir / "cec_summary.csv"
    fields = ["design", "arch", "mode", "Ksingle", "Idual", "Isharing", "Kdual", "status", "runtime_sec", "mapped", "blif", "log", "message"]
    with summary.open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fields)
        writer.writeheader()
        writer.writerows(
            sorted(
                rows,
                key=lambda row: (
                    row["design"],
                    archs.index(row["arch"]) if row["arch"] in archs else len(archs),
                    modes.index(row["mode"]) if row["mode"] in modes else len(modes),
                ),
            )
        )
    bad = [r for r in rows if r.get("status") != "pass"]
    print(f"wrote {summary}")
    if bad:
        print(f"CEC finished with {len(bad)} non-pass result(s)")
        return 2
    print("CEC passed for all requested results")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
