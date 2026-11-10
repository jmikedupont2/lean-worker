#!/usr/bin/env python3
"""Rebuild source fixtures and test JobVerifier (Lean 4.35)."""

import json
import os
from pathlib import Path
import subprocess
import sys

root = Path(__file__).resolve().parent
checker = root.parent / "Check.lean"
env = {**os.environ, "LEAN_PATH": str(root)}

def execute(args, label, timeout=90):
    try:
        proc = subprocess.run(
            args,
            cwd=root,
            env=env,
            text=True,
            capture_output=True,
            timeout=timeout,
            check=False,
        )
        rc, out, err = (
            proc.returncode,
            proc.stdout,
            proc.stderr,
        )
    except subprocess.TimeoutExpired as exc:
        rc, out, err = 124, "", str(exc)

    (root / (label + ".log")).write_text(
        "COMMAND=" + repr(args) + "\n"
        + "EXIT=" + str(rc) + "\n"
        + "STDOUT:\n" + out
        + "\nSTDERR:\n" + err + "\n"
    )
    return rc, out, err

print("=== LEAN VERSION ===", flush=True)
rc, version, err = execute(
    ["lean", "--version"], "lean_version", 15
)
print(version.strip(), flush=True)

if rc != 0 or not any(f"version {v}," in version for v in ("4.28.0", "4.35.0")):
    sys.exit("C32_LEAN_VERSION_MISMATCH")

print("=== COMPILE VERIFIER ===", flush=True)
rc, out, err = execute(
    ["lean", str(checker)], "checker_compile"
)

if rc != 0:
    print(out, err, flush=True)
    sys.exit("C32_CHECKER_COMPILE_FAILED")

print("C32_CHECKER_COMPILE=PASS", flush=True)

modules = [
    "Ref",
    "Good",
    "SorryCase",
    "AxiomCase",
    "Mismatch",
    "Missing",
    "DefCase",
    "UnusedAxiom",
    "ImportedOnly",
]

print("=== REBUILD ALL FIXTURES FROM SOURCE ===", flush=True)

for name in modules:
    rc, out, err = execute(
        ["lean", "-o", name + ".olean", name + ".lean"],
        "compile_" + name,
    )
    if rc != 0:
        print(name, out, err, flush=True)
        sys.exit("C32_FIXTURE_COMPILATION_FAILED_" + name)

    print("COMPILE_" + name + "=PASS", flush=True)

cases = [
    ("GOOD", "Good", "expected", 0, "OK"),
    ("SORRY", "SorryCase", "expected", 1, "SORRY"),
    ("AXIOM", "AxiomCase", "expected",
     1, "AXIOM_NOT_ALLOWED"),
    ("MISMATCH", "Mismatch", "expected",
     1, "STATEMENT_MISMATCH"),
    ("MISSING", "Missing", "expected",
     1, "TARGET_MISSING"),
    ("NOT_THEOREM", "DefCase", "expected",
     1, "TARGET_NOT_THEOREM"),
    ("UNUSED_AXIOM", "UnusedAxiom", "expected",
     1, "AXIOM_DECLARED"),
    ("IMPORTED", "ImportedOnly", "expected",
     1, "TARGET_MISSING"),
    ("REFERENCE_SPOOF", "Mismatch", "target",
     1, "REFERENCE_NOT_IN_MODULE"),
    ("IMPORT_FAILURE", "NonexistentC41Module", "expected",
     1, "IMPORT_FAILED"),
]

print("=== EXECUTE TEN REGRESSIONS ===", flush=True)

results = []

for label, module, expected, required_rc, required_reason in cases:

    command = [
        "lean", "--run", str(checker),
        "--module", module,
        "--decl", "target",
        "--ref", "Ref",
        "--expected", expected,
    ]

    rc, stdout, stderr = execute(
        command,
        "test_" + label,
        60,
    )

    verdict = {}

    try:
        lines = [
            line for line in stdout.splitlines()
            if line.strip()
        ]

        if len(lines) == 1:
            value = json.loads(lines[0])
            if isinstance(value, dict):
                verdict = value

    except (ValueError, TypeError):
        pass

    reason = verdict.get("reasonCode")

    passed = (
        rc == required_rc
        and reason == required_reason
        and verdict.get("schema") == "zos.verify.v1-testonly"
        and verdict.get("jobModule") == module
        and verdict.get("decl") == "target"
        and stderr == ""
    )

    results.append({
        "case": label,
        "exit": rc,
        "reason": reason,
        "passed": passed,
    })

    print(
        "CASE=" + label
        + " EXIT=" + str(rc)
        + " REASON=" + str(reason)
        + " STATUS=" + ("PASS" if passed else "FAIL"),
        flush=True,
    )

    if not passed:
        print("STDOUT:", stdout[:1500], flush=True)
        print("STDERR:", stderr[:1500], flush=True)

passed = sum(r["passed"] for r in results)

report = {
    "stage": "ZOS-INT-01-C32",
    "lean_version": version.strip(),
    "all_fixtures_rebuilt_from_source": True,
    "total": len(results),
    "passed": passed,
    "results": results,
    "real_worker_tested": False,
    "p2p_network_tested": False,
    "sandbox_provided": False,
}

(root / "REPORT.json").write_text(
    json.dumps(report, indent=2) + "\n"
)

print(f"C32_TESTS={passed}/{len(results)}", flush=True)

if passed != len(results):
    sys.exit("C32_REGRESSION_GATE_FAILED")

print("C32_REPRODUCIBLE_TEST_SUITE=PASS", flush=True)
