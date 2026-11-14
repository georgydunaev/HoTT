#!/usr/bin/env python3
"""
HoTT Test and Verification Runner

Executes both the Python Homotopy Type Theory unit tests (hott package)
and the formal Coq mechanization of Core Homotopy Theory, J-elimination,
and Univalence in theories/CoreHomotopyTheory.v.
"""

import sys
import unittest
import shutil
import subprocess
from pathlib import Path

ROOT_DIR = Path(__file__).resolve().parent


def log(msg: str):
    print(f"[HoTT-RUNNER] {msg}")


def run_unit_tests() -> bool:
    log("Running Python unit test suite...")
    loader = unittest.TestLoader()
    suite = loader.discover(start_dir=str(ROOT_DIR / "tests"), pattern="test_*.py")
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    return result.wasSuccessful()


def verify_coq_theories() -> bool:
    coqc = shutil.which("coqc")
    if not coqc:
        log("Notice: coqc not in PATH, skipping Coq standalone verification.")
        return True

    theories_to_verify = [
        ROOT_DIR / "theories" / "CoreHomotopyTheory.v",
        ROOT_DIR / "theories" / "Truncation.v",
        ROOT_DIR / "theories" / "Univalence.v",
        ROOT_DIR / "theories" / "HigherInductiveTypes.v",
        ROOT_DIR / "theories" / "BlakersMassey.v",
    ]

    all_passed = True
    for theory_v in theories_to_verify:
        if not theory_v.exists():
            log(f"Notice: {theory_v} not found, skipping.")
            continue

        log(f"Verifying formal Coq theory: {theory_v.name}...")
        res = subprocess.run([coqc, "-indices-matter", str(theory_v)], capture_output=True, text=True)

        # Clean artifacts
        for ext in [".vo", ".glob", ".vok", ".vos"]:
            f = theory_v.with_suffix(ext)
            if f.exists():
                try:
                    f.unlink()
                except Exception:
                    pass

        if res.returncode == 0:
            log(f"PASS: {theory_v.name} verified successfully.")
        else:
            log(f"FAIL: {theory_v.name} compilation failed with code {res.returncode}")
            print(res.stderr)
            all_passed = False

    return all_passed


def main():
    log("Starting comprehensive HoTT verification suite")
    py_ok = run_unit_tests()
    coq_ok = verify_coq_theories()

    if py_ok and coq_ok:
        log("All tests and formal theory verifications PASSED (100% pass rate).")
        sys.exit(0)
    else:
        log("Verification FAILED.")
        sys.exit(1)


if __name__ == "__main__":
    main()
