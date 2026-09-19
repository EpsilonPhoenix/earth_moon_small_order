#!/usr/bin/env python3
"""Build the pinned Lean project and audit the three printed theorem dependencies.

Uses only Python's standard library. A missing toolchain, failed command, missing
axiom report, or nonstandard axiom is never recorded as a successful check.
This checks the existing conditional formalization, not its open hypotheses.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
AUDITED_THEOREMS = (
    "EarthMoon.diamond_lists_colorable",
    "EarthMoon.dense17_obstruction_triangle_free",
    "EarthMoon.nine_colorable_through18_of_inputs",
)


def audit_axioms(output: str) -> dict[str, list[str]]:
    """Require actual #print axioms output; accept only standard foundations."""
    reports: dict[str, list[str]] = {}
    for match in re.finditer(
        r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",
        output,
    ):
        name, raw = match.groups()
        axioms = sorted({item.strip() for item in (raw or "").split(",") if item.strip()})
        if name in reports and reports[name] != axioms:
            raise ValueError(f"Conflicting axiom reports for {name}")
        reports[name] = axioms
    if re.search(r"\bsorryAx\b|declaration uses ['`]sorry['`]", output):
        raise ValueError("Lean output contains a sorry dependency or warning")
    for name in AUDITED_THEOREMS:
        if name not in reports:
            raise ValueError(f"Missing #print axioms report for {name}")
    for name, axioms in reports.items():
        unexpected = set(axioms) - ALLOWED_AXIOMS
        if unexpected:
            raise ValueError(f"Unexpected axioms for {name}: {sorted(unexpected)}")
    return {name: reports[name] for name in AUDITED_THEOREMS}


def verify_lean_version(output: str, toolchain: str) -> str:
    """Check the active compiler against the repository pin, not global Elan."""
    prefix = "leanprover/lean4:v"
    if not toolchain.startswith(prefix):
        raise ValueError(f"Expected an exact Lean version pin, got {toolchain!r}")
    expected = toolchain.removeprefix(prefix)
    match = re.search(r"\bversion\s+([^,\s)]+)", output)
    if match is None or match.group(1) != expected:
        raise ValueError(f"Active Lean does not match {toolchain}: {output.strip()}")
    return match.group(1)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "lean_verification.json")
    parser.add_argument("--timeout", type=int, default=600, help="Seconds per subprocess")
    args = parser.parse_args()
    if args.timeout <= 0:
        parser.error("--timeout must be positive")
    report: dict = {
        "schema_version": 1,
        "provenance": "local_execution",
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "status": "running",
        "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "source_sha256": {
            name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
            for name in ("SmallOrder.lean", "lean-toolchain", "lakefile.toml", "check_lean.py")
        },
        "formalization": "partial; conditional on GraphReductionInputs and FiniteCaseInputs",
        "planarity": "abstract PlanarPredicate; no concrete instantiation in this project",
        "checks": [],
    }

    def save() -> None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + "\n")

    def run(name: str, command: list[str]) -> str:
        print(f"=== {name}: {' '.join(command)} ===", flush=True)
        start = time.perf_counter()
        record = {"name": name, "command": command, "status": "running"}
        report["checks"].append(record)
        save()
        try:
            result = subprocess.run(command, cwd=ROOT, capture_output=True,
                                    text=True, encoding="utf-8", errors="replace",
                                    timeout=args.timeout)
        except subprocess.TimeoutExpired as exc:
            def text(value: str | bytes | None) -> str:
                return value.decode(errors="replace") if isinstance(value, bytes) else value or ""
            record.update(status="timeout", seconds=time.perf_counter() - start,
                          stdout=text(exc.stdout), stderr=text(exc.stderr))
            raise RuntimeError(f"{name}: exceeded {args.timeout} seconds") from exc
        except OSError as exc:
            record.update(status="failed", error=str(exc), seconds=time.perf_counter() - start)
            raise RuntimeError(f"{name}: {exc}") from exc
        record.update(status="passed" if result.returncode == 0 else "failed",
                      returncode=result.returncode, seconds=time.perf_counter() - start,
                      stdout=result.stdout, stderr=result.stderr)
        print(result.stdout, end="")
        print(result.stderr, end="", file=sys.stderr)
        save()
        if result.returncode:
            raise RuntimeError(f"{name}: exit status {result.returncode}")
        return result.stdout + "\n" + result.stderr

    lake = shutil.which("lake")
    if lake is None:
        report.update(status="not_run", reason="No Lake executable in PATH")
        save()
        print("Lean check not run: install the pinned toolchain and retry.", file=sys.stderr)
        return 2
    try:
        lean_version = run("lean_version", [lake, "env", "lean", "--version"])
        report["lean_version"] = verify_lean_version(lean_version, report["toolchain"])
        run("lake_version", [lake, "--version"])
        run("lean_build", [lake, "build"])
        output = run("lean_source_check", [lake, "env", "lean", "SmallOrder.lean"])
        report["axiom_dependencies"] = audit_axioms(output)
        report["status"] = "passed"
    except (RuntimeError, ValueError) as exc:
        report.update(status="failed", reason=str(exc))
        print(str(exc), file=sys.stderr)
    finally:
        report["finished_utc"] = datetime.now(timezone.utc).isoformat()
        save()
    if report["status"] != "passed":
        return 1
    print("PASS: pinned Lean build, direct source check, and three theorem axiom audits.")
    print("The final theorem remains conditional on its stated inputs.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
