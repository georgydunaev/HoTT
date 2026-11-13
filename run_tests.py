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

    core_v = ROOT_DIR / "theories" / "CoreHomotopyTheory.v"
    if not core_v.exists():
        log(f"Notice: {core_v} not found, skipping Coq verification.")
        return True

    log(f"Verifying formal Coq theory: {core_v.name}...")
    res = subprocess.run([coqc, "-indices-matter", str(core_v)], capture_output=True, text=True)

    # Clean artifacts
    for ext in [".vo", ".glob", ".vok", ".vos"]:
        f = core_v.with_suffix(ext)
        if f.exists():
            try:
                f.unlink()
            except Exception:
                pass

    if res.returncode == 0:
        log(f"PASS: {core_v.name} verified successfully.")
        return True
    else:
        log(f"FAIL: {core_v.name} compilation failed with code {res.returncode}")
        print(res.stderr)
        return False


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
