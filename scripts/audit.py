#!/usr/bin/env python3
"""Compile technical inspections and enforce their recursive-axiom allowlist."""
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import argparse
import json
import os
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
REPORT = re.compile(
    r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|"
    r"does not depend on any axioms)",
    re.MULTILINE,
)


def inspect(path):
    output_dir = ROOT / ".verification" / "audits"
    output_dir.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    env["PATH"] = str(Path.home() / ".elan/bin") + ":" + env.get("PATH", "")
    expected = len(re.findall(r"^#print axioms\s+", path.read_text(), re.MULTILINE))
    problems = []
    try:
        result = subprocess.run(
            ["lake", "env", "lean", "-DwarningAsError=true", str(path.relative_to(ROOT))],
            cwd=ROOT, env=env, text=True, stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, timeout=240,
        )
        output = result.stdout
        if result.returncode:
            problems.append(f"Lean exit {result.returncode}")
    except (OSError, subprocess.TimeoutExpired) as exc:
        output = str(exc)
        problems.append(type(exc).__name__)
    reports = list(REPORT.finditer(output))
    axioms = {
        axiom.strip()
        for match in reports
        for axiom in (match.group(2) or "").split(",")
        if axiom.strip()
    }
    if not expected or len(reports) != expected:
        problems.append(f"axiom reports {len(reports)}/{expected}")
    unexpected = axioms - ALLOWED
    if unexpected:
        problems.append("unexpected axioms: " + ", ".join(sorted(unexpected)))
    log = output_dir / (path.stem + ".log")
    log.write_text(output)
    return {
        "file": str(path.relative_to(ROOT)),
        "reports": len(reports),
        "expected_reports": expected,
        "axioms": sorted(axioms),
        "problems": problems,
        "log": str(log.relative_to(ROOT)),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jobs", type=int, default=2)
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    for checker in ["check_annotations.py", "check_interface.py"]:
        alignment = subprocess.run(
            [sys.executable, str(ROOT / "scripts" / checker)], cwd=ROOT
        )
        if alignment.returncode:
            return alignment.returncode
    paths = sorted((ROOT / "Audit").glob("*.lean"))
    if not paths:
        sys.exit("No audit files found")
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        results = list(pool.map(inspect, paths))
    for result in results:
        status = "FAIL" if result["problems"] else "PASS"
        detail = "; ".join(result["problems"]) or f'{result["reports"]} axiom reports'
        print(f'{status} {result["file"]}: {detail}', flush=True)
    summary = ROOT / ".verification" / "audits" / "summary.json"
    summary.write_text(json.dumps(results, indent=2) + "\n")
    print("Logs:", summary.parent.relative_to(ROOT))
    return 1 if any(result["problems"] for result in results) else 0


if __name__ == "__main__":
    sys.exit(main())