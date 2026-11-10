# JobVerifier regression tests

Requirements:
- Lean 4.28.0 or Lean 4.35.0
- Python 3

Run from this directory:

    python3 run_regressions.py

The runner compiles the checker and rebuilds nine fixture
modules from Lean sources. It then executes ten checks,
including a missing-module import failure.

The checker under test is ../Check.lean.

Security limitations:
- TEST_ONLY
- No sandbox
- No production worker integration
- No live P2P verification
- Reference module authorization belongs to the caller
