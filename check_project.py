#!/usr/bin/env python3
"""Run the reproducible checks; record Lean compilation separately.

Default: run arithmetic, enumerations, base coverage, MILP, and exact SMT.
--skip-smt skips only the shared-libz3 check.
--require-lean additionally requires the pinned build and theorem axiom audit.
Without --require-lean, the Lean audit is attempted when Lake is available and
otherwise explicitly recorded as not run. No unavailable check is a pass.
"""
from __future__ import annotations

import argparse
import hashlib
from importlib.metadata import version as package_version
import json
from pathlib import Path
import platform
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent


def check_lean_literals() -> dict:
    """Check embedded graph/coloring data without claiming to compile Lean."""
    source = (ROOT / "SmallOrder.lean").read_text()

    def block(name: str) -> str:
        match = re.search(rf"private def {name}\b.*?\n(?=(?:private )?def |theorem |/-!)", source, re.S)
        if not match:
            raise RuntimeError(f"Missing Lean literal definition: {name}")
        return match.group()

    def branches(name: str) -> list[list[int]]:
        return [json.loads(s) for s in re.findall(r"=>\s*(\[[\d,\s]*\])", block(name))]

    def single(name: str) -> list[int]:
        match = re.search(r":=\s*(\[[\d,\s]*\])", block(name))
        if not match:
            raise RuntimeError(f"Malformed list definition: {name}")
        return json.loads(match.group(1))

    def graph(rows: list[int]) -> set[tuple[int, int]]:
        n = len(rows)
        for u in range(n):
            if rows[u] < 0 or rows[u] >= 1 << n or rows[u] >> u & 1:
                raise RuntimeError("Invalid adjacency row")
            for v in range(n):
                if (rows[u] >> v & 1) != (rows[v] >> u & 1):
                    raise RuntimeError("Asymmetric adjacency table")
        return {(u, v) for u in range(n) for v in range(u + 1, n) if rows[u] >> v & 1}

    def triangle_free(rows: list[int]) -> bool:
        return all(not (rows[u] & rows[v]) for u, v in graph(rows))

    bases, colorings = branches("baseMasks"), branches("baseColorList")
    if len(bases) != 4 or len(colorings) != 4:
        raise RuntimeError("Expected four literal bases and four colorings")
    sizes = []
    for rows, colors in zip(bases, colorings):
        if len(rows) != 13 or len(colors) != 13 or set(colors) != set(range(7)):
            raise RuntimeError("Wrong literal base or coloring dimensions")
        edges = graph(rows)
        if any(colors[u] == colors[v] for u, v in edges):
            raise RuntimeError("Improper literal base coloring")
        complement = [((1 << 13) - 1) ^ row ^ (1 << u) for u, row in enumerate(rows)]
        if not triangle_free(complement):
            raise RuntimeError("Literal base has an independent triple")
        sizes.append(len(edges))
    if sizes != [41, 41, 41, 42]:
        raise RuntimeError(f"Unexpected base edge counts: {sizes}")
    cone, obstruction = single("coneMasks"), single("obstructionMasks")
    cone_edges, obstruction_edges = graph(cone), graph(obstruction)
    if len(cone) != 18 or len(obstruction) != 18 or len(obstruction_edges) != 65:
        raise RuntimeError("Wrong obstruction dimensions")
    if not obstruction_edges <= cone_edges or not triangle_free(obstruction):
        raise RuntimeError("Invalid literal density obstruction")
    # This lexical check is useful hygiene, not a proof audit or Lean parsing.
    stripped = re.sub(r"/-.*?-/", "", source, flags=re.S)
    stripped = re.sub(r"--[^\n]*", "", stripped)
    for token in ("sorry", "admit", "axiom", "native_decide", "unsafe"):
        if re.search(rf"\b{token}\b", stripped):
            raise RuntimeError(f"Disallowed proof shortcut token: {token}")
    return {"status": "passed", "base_edges": sizes, "obstruction_edges": 65,
            "scope": "literal data and lexical hygiene only; not Lean elaboration"}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--skip-smt", action="store_true")
    parser.add_argument("--require-lean", action="store_true")
    args = parser.parse_args()
    if not __debug__:
        raise RuntimeError("Run without -O")
    records = []
    report: dict = {
        "provenance": "local_execution",
        "python_version": platform.python_version(), "checks": records,
        "package_versions": {name: package_version(name) for name in ("networkx", "numpy", "scipy")},
        "formalization": "partial; final theorem requires GraphReductionInputs and FiniteCaseInputs",
        "earlier_user_build_record": "verification/lean-4.34.0-user-build.json",
        "lean_compilation": "not_run",
        "lean_axiom_audit": "not_run",
        "source_sha256": {
            str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in sorted({
                *ROOT.glob("*.lean"), *ROOT.glob("*.py"),
                *(ROOT / "computations").glob("*.py"),
                ROOT / "lean-toolchain", ROOT / "lakefile.toml",
            })
        },
    }

    def save() -> None:
        (ROOT / "verification.json").write_text(json.dumps(report, indent=2) + "\n")

    def run(label: str, command: list[str], timeout: int = 600) -> None:
        print(f"=== {label} ===", flush=True)
        start = time.perf_counter()
        try:
            completed = subprocess.run(command, cwd=ROOT, text=True,
                                       capture_output=True, timeout=timeout)
        except subprocess.TimeoutExpired as error:
            def text(value: str | bytes | None) -> str:
                return value.decode(errors="replace") if isinstance(value, bytes) else value or ""
            records.append({"name": label, "command": command, "status": "timeout",
                            "seconds": time.perf_counter() - start,
                            "stdout": text(error.stdout), "stderr": text(error.stderr)})
            save()
            raise SystemExit(f"{label}: timed out; no successful result recorded") from error
        records.append({"name": label, "command": command,
                        "status": "passed" if completed.returncode == 0 else "failed",
                        "returncode": completed.returncode,
                        "seconds": time.perf_counter() - start,
                        "stdout": completed.stdout, "stderr": completed.stderr})
        save()
        if completed.returncode:
            print(completed.stdout, end="")
            print(completed.stderr, end="", file=sys.stderr)
            raise SystemExit(completed.returncode)
        print("passed", flush=True)

    run("arithmetic", [sys.executable, "arithmetic_check.py", "--json", "computations/arithmetic_results.json"])
    for script in ["verify_dense17_independent.py", "verify_mtf13_independent.py", "verify_B7_catalogue.py",
                   "verify_attachment_base_coverage.py", "verify_sat_independent.py"]:
        run(script.removesuffix(".py"), [sys.executable, f"computations/{script}"])
    if args.skip_smt:
        records.append({"name": "exact_smt", "status": "not_run", "reason": "--skip-smt"})
    else:
        run("exact_smt", [sys.executable, "computations/verify_exact_smt.py"])
    report["lean_literals"] = check_lean_literals()
    lake = shutil.which("lake")
    if lake:
        report["lean_compilation"] = "running"
        report["lean_axiom_audit"] = "running"
        save()
        local_lean_report = ROOT / "lean_verification.json"
        # Prevent an earlier report from being mistaken for this execution.
        local_lean_report.unlink(missing_ok=True)
        try:
            run("lean_build_and_axiom_audit", [sys.executable, "check_lean.py"])
        finally:
            report["lean_compilation"] = "not_run"
            report["lean_axiom_audit"] = "failed"
            if local_lean_report.exists():
                lean_result = json.loads(local_lean_report.read_text())
                builds = [step for step in lean_result.get("checks", [])
                          if step["name"] == "lean_build"]
                if builds:
                    report["lean_compilation"] = builds[-1]["status"]
                report["lean_axiom_audit"] = lean_result["status"]
                report["lean_report"] = "lean_verification.json"
            save()
    else:
        report["lean_compilation_reason"] = "No Lean/Lake executable in PATH for this run"
    report["external_checks"] = "passed_smt_skipped" if args.skip_smt else "passed"
    save()
    if args.require_lean and not lake:
        raise SystemExit("Lean check required but not run: install the pinned toolchain and retry")
    print("Python checks passed. Lean compilation:", report["lean_compilation"])


if __name__ == "__main__":
    main()
