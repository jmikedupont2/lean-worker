# JobVerifier regression tests

Requires Lean 4.35.0 and Python 3.

Run:

    python3 run_regressions.py

The runner compiles all nine Lean fixture modules from
source and executes nine verifier checks.

The checker under test is ../Check.lean.

Security limits:
- TEST_ONLY
- No sandboxing or production worker integration
- No real P2P network verification
- Caller must authorize the reference module
