#!/usr/bin/env python3
"""
Simplification-correctness fuzzer for CSB.

CSB disables every STP simplification when running in counting/sampling mode,
because some simplifications can change the model count. This script identifies
which simplifications can safely be turned back on without changing the count.

Strategy:
  1. Generate a corpus of QF_BV SMT-LIB2 formulas using smtfuzz, plus the
     in-tree tests/examples/*.smt2 as a regression set.
  2. For each formula: run CSB with all simplifications off (baseline) and
     record the answer ("s mc N" or "unsat").
  3. Stage A (solo): for each candidate simplification flag, re-run CSB with
     --enable-simp=<flag> and compare to baseline. Any disagreement is logged.
  4. Stage B (greedy combine): take the subset of flags that never disagreed
     in Stage A and run them all together. If they still agree, this is the
     largest "safe" subset. Otherwise, drop to pairwise testing to localize.

Outputs:
  - per-flag JSON summary in <out>/summary.json
  - failing inputs copied to <out>/reports/ with the offending flag in the name
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional


# The flags that disableSimplifications() turns off in counting/sampling mode.
# Keep in sync with the --enable-simp name table in tools/stp/main.cpp.
FLAGS = [
    "optimize",
    "unconstrained",
    "cbitp",
    "intervals",
    "pure-literals",
    "always-true",
    "wordlevel",
    "equality",
    "flatten",
    "split-extracts",
    "rewriting",
    "merge-same",
    "ite-context",
    "bitblast-simp",
]


@dataclass
class CsbResult:
    status: str  # "mc", "unsat", "timeout", "error", "no-output"
    count: Optional[str] = None  # decimal string for "mc"; None otherwise
    stderr_tail: str = ""

    def key(self) -> tuple[str, Optional[str]]:
        return (self.status, self.count)


def run_csb(csb: str, smt2: Path, enable: Optional[str], timeout_s: int,
            disable_all: bool = False) -> CsbResult:
    cmd = [csb]
    if disable_all:
        cmd.append("--disable-simplifications")
    if enable:
        cmd.append(f"--enable-simp={enable}")
    cmd.append(str(smt2))
    try:
        p = subprocess.run(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=timeout_s,
            text=True,
        )
    except subprocess.TimeoutExpired:
        return CsbResult(status="timeout")

    out = p.stdout
    err = (p.stderr or "")[-400:]

    # Look for "s mc <number>" first (counting mode).
    for line in out.splitlines():
        m = re.match(r"^s\s+mc\s+(\S+)\s*$", line)
        if m:
            return CsbResult(status="mc", count=m.group(1), stderr_tail=err)
    # Otherwise look for a bare "unsat".
    for line in out.splitlines():
        if line.strip() == "unsat":
            return CsbResult(status="unsat", stderr_tail=err)
        if line.strip() == "sat":
            # CSB shouldn't print just "sat" in counting mode but handle defensively.
            return CsbResult(status="sat", stderr_tail=err)

    return CsbResult(status="no-output", stderr_tail=err)


def gen_smtfuzz(python: str, out_dir: Path, n: int, seed_start: int,
                logic: str = "QF_BV") -> list[Path]:
    """Generate `n` fuzz inputs using smtfuzz. Returns the list of file paths."""
    out_dir.mkdir(parents=True, exist_ok=True)
    files: list[Path] = []
    for i in range(n):
        seed = seed_start + i
        f = out_dir / f"fuzz_s{seed}.smt2"
        cmd = [
            python, "-c", "from smtfuzz.smtfuzz import main; main()",
            "--logic", logic,
            "--strategy", "noinc",
            "--seed", str(seed),
        ]
        try:
            p = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                               timeout=30, text=True)
        except subprocess.TimeoutExpired:
            continue
        if p.returncode != 0 or not p.stdout.strip():
            continue
        f.write_text(p.stdout)
        files.append(f)
    return files


@dataclass
class FormulaOutcome:
    path: str
    baseline: tuple[str, Optional[str]]
    per_flag: dict[str, tuple[str, Optional[str]]] = field(default_factory=dict)


@dataclass
class FlagStats:
    agree: int = 0
    disagree: int = 0
    timeout: int = 0
    error: int = 0
    no_output: int = 0
    sample_disagreements: list[str] = field(default_factory=list)


def stage_solo(csb: str, formulas: list[Path], timeout_s: int,
               report_dir: Path) -> tuple[dict[str, FlagStats], list[FormulaOutcome]]:
    stats = {f: FlagStats() for f in FLAGS}
    outcomes: list[FormulaOutcome] = []
    report_dir.mkdir(parents=True, exist_ok=True)

    for idx, formula in enumerate(formulas, start=1):
        print(f"[{idx}/{len(formulas)}] {formula.name}", flush=True)
        # Gold-standard baseline: everything off. Comparison runs always start
        # from the same "all off" state and re-enable a single simplification.
        base = run_csb(csb, formula, enable=None, timeout_s=timeout_s,
                       disable_all=True)
        if base.status not in ("mc", "unsat"):
            print(f"  baseline {base.status}; skipping formula", flush=True)
            continue
        outcome = FormulaOutcome(path=str(formula), baseline=base.key())
        print(f"  baseline: {base.status}{(' ' + base.count) if base.count else ''}",
              flush=True)
        # Test 1: the new counting-mode default (all safe simps on).
        r_default = run_csb(csb, formula, enable=None, timeout_s=timeout_s)
        outcome.per_flag["__default__"] = r_default.key()
        s_default = stats.setdefault("__default__", FlagStats())
        if r_default.status == "timeout":
            s_default.timeout += 1
        elif r_default.status in ("no-output", "error"):
            s_default.no_output += (1 if r_default.status == "no-output" else 0)
            s_default.error += (1 if r_default.status == "error" else 0)
            s_default.disagree += 1
            if len(s_default.sample_disagreements) < 3:
                s_default.sample_disagreements.append(formula.name)
            dst = report_dir / f"default__{formula.name}"
            try:
                shutil.copy(formula, dst)
                (dst.with_suffix(".smt2.diff.txt")).write_text(
                    f"baseline: {base.status} {base.count}\n"
                    f"default (safe simps on): {r_default.status} (no answer)\n"
                    f"stderr_tail:\n{r_default.stderr_tail}\n"
                )
            except OSError:
                pass
            print(f"  DEFAULT regression: base={base.key()} got={r_default.status}",
                  flush=True)
        elif r_default.key() == base.key():
            s_default.agree += 1
        else:
            s_default.disagree += 1
            if len(s_default.sample_disagreements) < 3:
                s_default.sample_disagreements.append(formula.name)
            dst = report_dir / f"default__{formula.name}"
            try:
                shutil.copy(formula, dst)
                (dst.with_suffix(".smt2.diff.txt")).write_text(
                    f"baseline: {base.status} {base.count}\n"
                    f"default (safe simps on): {r_default.status} {r_default.count}\n"
                    f"stderr_tail:\n{r_default.stderr_tail}\n"
                )
            except OSError:
                pass
            print(f"  DEFAULT disagree: base={base.key()} got={r_default.key()}",
                  flush=True)
        for flag in FLAGS:
            # Run with the gold-standard "all off" baseline + single flag on,
            # so each flag is exercised in isolation.
            r = run_csb(csb, formula, enable=flag, timeout_s=timeout_s,
                        disable_all=True)
            outcome.per_flag[flag] = r.key()
            s = stats[flag]
            # A candidate that no-output's or errors out while the baseline
            # produced an answer is a real regression: the answer changed
            # from "mc N" / "unsat" to "(nothing)". Count it as a disagreement.
            if r.status == "timeout":
                s.timeout += 1
            elif r.status in ("no-output", "error"):
                if r.status == "no-output":
                    s.no_output += 1
                else:
                    s.error += 1
                s.disagree += 1
                if len(s.sample_disagreements) < 3:
                    s.sample_disagreements.append(formula.name)
                dst = report_dir / f"{flag}__{formula.name}"
                try:
                    shutil.copy(formula, dst)
                    (dst.with_suffix(".smt2.diff.txt")).write_text(
                        f"baseline: {base.status} {base.count}\n"
                        f"with --enable-simp={flag}: {r.status} (no answer)\n"
                        f"stderr_tail:\n{r.stderr_tail}\n"
                    )
                except OSError:
                    pass
                print(f"  REGRESSION on {flag}: base={base.key()} got={r.status}",
                      flush=True)
            elif r.key() == base.key():
                s.agree += 1
            else:
                s.disagree += 1
                if len(s.sample_disagreements) < 3:
                    s.sample_disagreements.append(formula.name)
                dst = report_dir / f"{flag}__{formula.name}"
                try:
                    shutil.copy(formula, dst)
                    (dst.with_suffix(".smt2.diff.txt")).write_text(
                        f"baseline: {base.status} {base.count}\n"
                        f"with --enable-simp={flag}: {r.status} {r.count}\n"
                        f"stderr_tail:\n{r.stderr_tail}\n"
                    )
                except OSError:
                    pass
                print(f"  DISAGREE on {flag}: base={base.key()} got={r.key()}",
                      flush=True)
        outcomes.append(outcome)
    return stats, outcomes


def stage_combine(csb: str, formulas: list[Path], safe_flags: list[str],
                  timeout_s: int, report_dir: Path) -> dict[str, FlagStats]:
    """Run all safe_flags together and confirm agreement. On disagreement,
    drop to pairwise to find the smallest breaking subset.

    Returns a stats dict keyed by the combined flag string and any pair strings
    that were tested.
    """
    combined = ",".join(safe_flags)
    combo_stats = {combined: FlagStats()}
    pair_stats: dict[str, FlagStats] = {}
    if not safe_flags:
        print("Stage B: no safe flags found in Stage A; skipping.", flush=True)
        return combo_stats

    print(f"Stage B: combining {len(safe_flags)} safe flags: {combined}", flush=True)
    bad_formulas: list[Path] = []
    for idx, formula in enumerate(formulas, start=1):
        base = run_csb(csb, formula, enable=None, timeout_s=timeout_s,
                       disable_all=True)
        if base.status not in ("mc", "unsat"):
            continue
        r = run_csb(csb, formula, enable=combined, timeout_s=timeout_s,
                    disable_all=True)
        s = combo_stats[combined]
        if r.status == "timeout":
            s.timeout += 1
        elif r.status in ("no-output", "error"):
            if r.status == "no-output":
                s.no_output += 1
            else:
                s.error += 1
            s.disagree += 1
            bad_formulas.append(formula)
            if len(s.sample_disagreements) < 3:
                s.sample_disagreements.append(formula.name)
            dst = report_dir / f"combined__{formula.name}"
            try:
                shutil.copy(formula, dst)
                (dst.with_suffix(".smt2.diff.txt")).write_text(
                    f"baseline: {base.status} {base.count}\n"
                    f"with --enable-simp={combined}: {r.status} (no answer)\n"
                    f"stderr_tail:\n{r.stderr_tail}\n"
                )
            except OSError:
                pass
            print(f"  COMBO REGRESSION on {formula.name}: base={base.key()} got={r.status}",
                  flush=True)
        elif r.key() == base.key():
            s.agree += 1
        else:
            s.disagree += 1
            bad_formulas.append(formula)
            if len(s.sample_disagreements) < 3:
                s.sample_disagreements.append(formula.name)
            dst = report_dir / f"combined__{formula.name}"
            try:
                shutil.copy(formula, dst)
                (dst.with_suffix(".smt2.diff.txt")).write_text(
                    f"baseline: {base.status} {base.count}\n"
                    f"with --enable-simp={combined}: {r.status} {r.count}\n"
                    f"stderr_tail:\n{r.stderr_tail}\n"
                )
            except OSError:
                pass
            print(f"  COMBO DISAGREE on {formula.name}: base={base.key()} got={r.key()}",
                  flush=True)
        print(f"  [combine {idx}/{len(formulas)}] {formula.name}: {r.status}",
              flush=True)

    # Pairwise localization on the first few breaking formulas.
    if bad_formulas:
        print(f"Stage B fallback: pairwise on {min(3, len(bad_formulas))} broken inputs",
              flush=True)
        for formula in bad_formulas[:3]:
            base = run_csb(csb, formula, enable=None, timeout_s=timeout_s,
                           disable_all=True)
            for i in range(len(safe_flags)):
                for j in range(i + 1, len(safe_flags)):
                    pair = f"{safe_flags[i]},{safe_flags[j]}"
                    r = run_csb(csb, formula, enable=pair, timeout_s=timeout_s,
                                disable_all=True)
                    s = pair_stats.setdefault(pair, FlagStats())
                    if r.status in ("mc", "unsat") and r.key() != base.key():
                        s.disagree += 1
                        if len(s.sample_disagreements) < 3:
                            s.sample_disagreements.append(formula.name)
                    elif r.status in ("mc", "unsat"):
                        s.agree += 1
                    elif r.status == "timeout":
                        s.timeout += 1
                    else:
                        s.error += 1

    return {**combo_stats, **pair_stats}


def collect_examples(examples_dir: Path) -> list[Path]:
    return sorted(p for p in examples_dir.glob("*.smt2") if p.is_file())


def main(argv: Optional[list[str]] = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--csb", default=str(Path(__file__).resolve().parents[2]
                                         / "result" / "bin" / "csb"),
                    help="Path to csb binary (default: ../../result/bin/csb)")
    ap.add_argument("--python", default=str(Path(__file__).resolve().parent
                                            / ".venv" / "bin" / "python"),
                    help="Python interpreter with smtfuzz installed (default: ./.venv/bin/python)")
    ap.add_argument("--examples", default=str(Path(__file__).resolve().parents[2]
                                              / "tests" / "examples"),
                    help="Regression set directory (default: tests/examples)")
    ap.add_argument("--out", default=str(Path(__file__).resolve().parent / "out"),
                    help="Output directory")
    ap.add_argument("--num-fuzz", type=int, default=30,
                    help="Number of smtfuzz inputs to generate (default: 30)")
    ap.add_argument("--seed-start", type=int, default=1000,
                    help="Starting smtfuzz seed (default: 1000)")
    ap.add_argument("--logic", default="QF_BV",
                    help="smtfuzz --logic (default: QF_BV)")
    ap.add_argument("--timeout", type=int, default=15,
                    help="Per-CSB-call timeout in seconds (default: 15)")
    ap.add_argument("--skip-examples", action="store_true",
                    help="Skip the in-tree tests/examples regression set")
    ap.add_argument("--skip-fuzz", action="store_true",
                    help="Skip smtfuzz generation; only use --examples")
    args = ap.parse_args(argv)

    csb = args.csb
    if not Path(csb).exists():
        print(f"ERROR: csb binary not found at {csb}", file=sys.stderr)
        return 2
    if not args.skip_fuzz and not Path(args.python).exists():
        print(f"ERROR: python interpreter not found at {args.python}", file=sys.stderr)
        return 2

    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    fuzz_dir = out / "fuzz_inputs"
    report_dir = out / "reports"

    formulas: list[Path] = []
    if not args.skip_examples:
        formulas.extend(collect_examples(Path(args.examples)))
        print(f"Regression set: {len(formulas)} formulas from {args.examples}",
              flush=True)
    if not args.skip_fuzz:
        print(f"Generating {args.num_fuzz} smtfuzz inputs...", flush=True)
        gen = gen_smtfuzz(args.python, fuzz_dir, args.num_fuzz, args.seed_start,
                          logic=args.logic)
        print(f"Generated {len(gen)} fuzz formulas", flush=True)
        formulas.extend(gen)

    print(f"Stage A: solo, {len(formulas)} formulas x {len(FLAGS)} flags "
          f"= {len(formulas) * len(FLAGS)} CSB runs (+ baselines)", flush=True)
    t0 = time.time()
    stats, outcomes = stage_solo(csb, formulas, args.timeout, report_dir)
    t_solo = time.time() - t0

    safe = [f for f, s in stats.items() if s.disagree == 0 and s.agree > 0]
    print(f"Stage A done in {t_solo:.1f}s. Solo-safe flags: {safe}", flush=True)

    print("Per-flag solo summary:", flush=True)
    for f in FLAGS:
        s = stats[f]
        print(f"  {f:<16s} agree={s.agree:>4d} disagree={s.disagree:>3d} "
              f"timeout={s.timeout:>3d} no-output={s.no_output:>3d} error={s.error:>3d}",
              flush=True)

    combo_stats = stage_combine(csb, formulas, safe, args.timeout, report_dir)

    summary = {
        "csb": csb,
        "num_formulas": len(formulas),
        "timeout_s": args.timeout,
        "flags_tested": FLAGS,
        "solo": {f: stats[f].__dict__ for f in FLAGS},
        "solo_safe_flags": safe,
        "combine": {k: v.__dict__ for k, v in combo_stats.items()},
        "outcomes": [
            {"path": o.path, "baseline": list(o.baseline),
             "per_flag": {k: list(v) for k, v in o.per_flag.items()}}
            for o in outcomes
        ],
        "elapsed_solo_s": t_solo,
    }
    (out / "summary.json").write_text(json.dumps(summary, indent=2, default=str))
    print(f"Summary written to {out / 'summary.json'}", flush=True)
    print(f"Failure reports (if any) in {report_dir}", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
