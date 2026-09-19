#!/usr/bin/env python3
"""Regression tests for the check runner; these tests do not execute Lean."""
from __future__ import annotations

import contextlib
import io
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import check_lean
import check_project

OUTPUT = "\n".join(
    f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]"
    for name in check_lean.AUDITED_THEOREMS
)


class AuditTests(unittest.TestCase):
    def test_standard_axioms(self):
        self.assertEqual(len(check_lean.audit_axioms(OUTPUT)), 3)

    def test_info_prefix_and_wrapped_lists(self):
        output = "\n".join(f"info: SmallOrder.lean:1:0: {line}" for line in OUTPUT.splitlines())
        self.assertEqual(check_lean.audit_axioms(output.replace(", ", ",\n ")),
                         check_lean.audit_axioms(OUTPUT))

    def test_fewer_axioms_are_accepted(self):
        output = OUTPUT.replace("depends on axioms: [propext, Classical.choice, Quot.sound]",
                                "does not depend on any axioms")
        self.assertTrue(all(not xs for xs in check_lean.audit_axioms(output).values()))

    def test_sorry_is_rejected(self):
        with self.assertRaises(ValueError):
            check_lean.audit_axioms(OUTPUT.replace("propext", "sorryAx", 1))

    def test_custom_axiom_is_rejected(self):
        with self.assertRaises(ValueError):
            check_lean.audit_axioms(OUTPUT.replace("propext", "EarthMoon.unproved", 1))

    def test_missing_theorem_is_rejected(self):
        with self.assertRaises(ValueError):
            check_lean.audit_axioms(OUTPUT.splitlines()[0])

    def test_empty_output_is_rejected(self):
        with self.assertRaises(ValueError):
            check_lean.audit_axioms("")

    def test_inconsistent_duplicate_is_rejected(self):
        with self.assertRaises(ValueError):
            check_lean.audit_axioms(OUTPUT + "\n" + OUTPUT.splitlines()[0].replace(", Classical.choice", ""))

    def test_reported_version(self):
        self.assertEqual(check_lean.verify_lean_version(
            "Lean (version 4.34.0, x86_64-unknown-linux-gnu, commit 293d5d0c, Release)",
            "leanprover/lean4:v4.34.0"), "4.34.0")

    def test_wrong_version_is_rejected(self):
        with self.assertRaises(ValueError):
            check_lean.verify_lean_version("Lean (version 4.19.0, Release)",
                                          "leanprover/lean4:v4.34.0")


class RunnerTests(unittest.TestCase):
    def invoke(self, responses=None, *, lake="lake", exception=None):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "verification.json"
            with patch("sys.argv", ["check_lean.py", "--output", str(output)]), \
                 patch("check_lean.shutil.which", return_value=lake), \
                 patch("check_lean.subprocess.run", side_effect=exception or responses), \
                 contextlib.redirect_stdout(io.StringIO()), \
                 contextlib.redirect_stderr(io.StringIO()):
                status = check_lean.main()
            return status, json.loads(output.read_text())

    @staticmethod
    def commands(last_output=OUTPUT):
        return [subprocess.CompletedProcess([], 0, output, "") for output in (
            "Lean (version 4.34.0, Release)",
            "Lake version 5.0.0-src+293d5d0 (Lean version 4.34.0)",
            "Build completed successfully (3 jobs).\n", last_output)]

    def test_success(self):
        code, report = self.invoke(self.commands())
        self.assertEqual(code, 0)
        self.assertEqual(report["status"], "passed")
        self.assertEqual(len(report["checks"]), 4)
        self.assertEqual(len(report["axiom_dependencies"]), 3)

    def test_missing_lake_is_not_a_pass(self):
        code, report = self.invoke(lake=None)
        self.assertEqual(code, 2)
        self.assertEqual(report["status"], "not_run")

    def test_failed_build_is_recorded(self):
        responses = self.commands()
        responses[2] = subprocess.CompletedProcess([], 1, "", "error: build failed")
        code, report = self.invoke(responses)
        self.assertEqual(code, 1)
        self.assertEqual(report["status"], "failed")
        self.assertEqual(report["checks"][-1]["status"], "failed")

    def test_timeout_is_recorded(self):
        code, report = self.invoke(exception=subprocess.TimeoutExpired(["lake"], 600))
        self.assertEqual(code, 1)
        self.assertEqual(report["checks"][0]["status"], "timeout")

    def test_success_without_axiom_output_is_not_a_pass(self):
        code, report = self.invoke(self.commands(last_output=""))
        self.assertEqual(code, 1)
        self.assertEqual(report["status"], "failed")

    def test_success_with_sorry_is_not_a_pass(self):
        code, report = self.invoke(self.commands(last_output=OUTPUT.replace("propext", "sorryAx")))
        self.assertEqual(code, 1)
        self.assertEqual(report["status"], "failed")

    def test_oserror_is_recorded(self):
        code, report = self.invoke(exception=OSError("executable unavailable"))
        self.assertEqual(code, 1)
        self.assertEqual(report["checks"][0]["status"], "failed")


class ProjectIntegrationTests(unittest.TestCase):
    def invoke(self, *, lake="lake", lean_status="passed", build_status="passed", require=False):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name in ("lean-toolchain", "lakefile.toml"):
                (root / name).write_bytes((check_project.ROOT / name).read_bytes())
            (root / ".venv").mkdir()
            (root / ".venv" / "dependency.py").write_text("# not project source\n")
            stale = root / "lean_verification.json"
            stale.write_text('{"status": "passed", "checks": []}')
            arguments = ["check_project.py", "--skip-smt"]
            if require:
                arguments.append("--require-lean")

            def subprocess_result(command, **kwargs):
                if command[-1] == "check_lean.py":
                    self.assertFalse(stale.exists(), "Old Lean report must be removed")
                    stale.write_text(json.dumps({
                        "status": lean_status,
                        "checks": [{"name": "lean_build", "status": build_status}],
                    }))
                    return subprocess.CompletedProcess(command, 0 if lean_status == "passed" else 1, "", "")
                return subprocess.CompletedProcess(command, 0, "", "")

            with patch("sys.argv", arguments), \
                 patch("check_project.ROOT", root), \
                 patch("check_project.package_version", return_value="mock"), \
                 patch("check_project.check_lean_literals", return_value={"status": "passed"}), \
                 patch("check_project.shutil.which", return_value=lake), \
                 patch("check_project.subprocess.run", side_effect=subprocess_result), \
                 contextlib.redirect_stdout(io.StringIO()), \
                 contextlib.redirect_stderr(io.StringIO()):
                exit_code = 0
                try:
                    check_project.main()
                except SystemExit as exc:
                    exit_code = exc.code
            return exit_code, json.loads((root / "verification.json").read_text())

    def test_combined_success_and_source_scope(self):
        code, report = self.invoke()
        self.assertEqual(code, 0)
        self.assertEqual(report["lean_compilation"], "passed")
        self.assertEqual(report["lean_axiom_audit"], "passed")
        self.assertFalse(any(".venv" in name for name in report["source_sha256"]))

    def test_axiom_failure_keeps_successful_compilation(self):
        code, report = self.invoke(lean_status="failed")
        self.assertNotEqual(code, 0)
        self.assertEqual(report["lean_compilation"], "passed")
        self.assertEqual(report["lean_axiom_audit"], "failed")

    def test_combined_missing_lake(self):
        code, report = self.invoke(lake=None)
        self.assertEqual(code, 0)
        self.assertEqual(report["lean_compilation"], "not_run")

    def test_combined_require_lean_fails_when_missing(self):
        code, report = self.invoke(lake=None, require=True)
        self.assertNotEqual(code, 0)
        self.assertEqual(report["lean_compilation"], "not_run")


if __name__ == "__main__":
    unittest.main()
