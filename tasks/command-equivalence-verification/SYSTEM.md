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
1. [x] Fixed `leanWorker_caller_valid` to target actual `leanWorker_build_caller`
2. [x] Fixed `callerRegistry_allWellFormed` to actual registry entries
3. [x] Fixed `callerRegistry_has_verified_callers` for actual call count
4. [x] Fixed `find_lean_worker_callers` and `find_unknown_callers` for actual registry
5. [x] Code-reviewed proof theorems against the actual 13-entry `callerRegistry` + `verifiedCaller` model

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
- `minimal/lean_worker_registry.lean` defines the registry
- Fixed `VerifiedRunner` definitions (log_wellFormed, exitCode_nonNeg, etc.)

## Notes
- The `lean_worker_caller_combined.lean` file is a standalone combined model; it is not tracked in git (it is `MM` in git status, meaning it differs from both the index and HEAD).
- `minimal/Gokujo.lean`: recursive `scanStr`/`walkLean` replaced with iterative `scanStrTR`/`walkLeanTR` (Solfunmeme-scale 663-file scans).
- Native binary `minimal/gokujo` rebuilt (4,349,432 bytes, ELF 64-bit).
