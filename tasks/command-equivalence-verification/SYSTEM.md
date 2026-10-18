# Task: VerifiedRunner Command Equivalence Verification

**Status:** in_progress
**Project:** lean-worker
**Priority:** P1

## Description
Fix and verify the `verifiedRunner` proof theorems in `minimal/lean_worker_caller_combined.lean` so that the standalone Lean 4 compilation succeeds. The file proves that each gokujo caller (fetch, build, check, selfcheck, targets, release, bundle, init, poll, download, verify, sync, bootstrap) carries a verified task log with non-negative exit codes.

## Context
- The `verifiedRunner` predicate is the foundation of the lean-worker's formal model of gokujo invocations.
- The file `minimal/lean_worker_caller_combined.lean` was written to compile standalone with `lean` (no lake build system), combining `VerifiedRunner` and `LeanWorkerCaller` namespaces.
- The `leanWorker_caller_valid` theorem closed over `leanWorker_caller` (which does not exist in this combined file), and the `callerRegistry_allWellFormed` theorem was written against a different call count than the actual `callerRegistry`.

## Steps
1. [x] Fix `leanWorker_caller_valid` to target the actual `leanWorker_caller` (now `leanWorker_build_caller`)
2. [x] Fix `callerRegistry_allWellFormed` to match the actual `callerRegistry` (4 entries: fetch, build, check, bootstrap)
3. [x] Fix `callerRegistry_has_verified_callers` for the actual call count
4. [x] Fix `find_lean_worker_callers` and `find_unknown_callers` for the actual registry
5. [x] Verify the full file compiles with `lean minimal/lean_worker_caller_combined.lean`

## Commands
```bash
cd /mnt/data1/time-2026/09-september/18/lean-worker
leanc minimal/lean_worker_caller_combined.lean
```

## Verification
- `lean minimal/lean_worker_caller_combined.lean` exits with status 0 and no errors
- All 13 verifiedCaller theorems prove their respective callers valid
- `callerRegistry_allWellFormed` proves every caller in the registry is valid
- `callerRegistry_has_verified_callers` proves the registry is non-empty and has verified members

## Dependencies
- `minimal/lean_worker_caller.lean` exists with the `GokujoCaller` model
- `minimal/lean_worker_registry.lean` defines the registry with `leanWorker_caller`
- Fixed `VerifiedRunner` definitions (log_wellFormed, exitCode_nonNeg, etc.)

## Notes
- The `lean_worker_caller_combined.lean` file is a standalone copy of the combined model; it is not tracked in git (it is `MM` in git status, meaning it differs from both the index and HEAD).
- The `verifiedRunner` structure and the 13 gokujo callers are the same as in the tracked `lean_worker_caller.lean` and `lean_worker_registry.lean`, but the combined file was rewritten to be self-contained for standalone compilation.
