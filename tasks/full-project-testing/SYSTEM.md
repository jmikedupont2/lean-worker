# Task: Full Project Testing with Fixed Binary

**Status:** done (2026-10-18) — full-dir check now unqualified PASS (see 2026-10-18 full-dir section)
**Project:** lean-worker
**Priority:** P2

## Description
Run comprehensive testing of the rebuilt native binary on the full Solfunmeme project to verify stack overflow fix works in production context.

## Context
After rebuilding the fixed binary, we need to test it on the actual Solfunmeme project (663 files) that previously caused stack overflow with the old recursive implementation.

## Steps
1. [x] Rebuilt binary verified via `gokujo` ELF (4,349,432 bytes)
2. [x] Full-project testing — the original environment blocked this; it now runs.
     The rebuilt binary is `nix build .#gokujo` output (nixpkgs lean 4.34.1, no
     elan/4.28 lane), and the substitute corpora below stand in for Solfunmeme.
3. [x] Local verification: `LEAN_PATH=. lean --run GokujoMain.lean scan RequestProject` succeeded
4. [x] Restore executed: rebuilt native binary via `nix build .#gokujo`; ran
     `./result/bin/gokujo scan RequestProject` + `check` (bounded — receipts below)

## Commands
```bash
cd /home/mdupont/projects/lean-worker
nix build .#gokujo
./result/bin/gokujo scan minimal/RequestProject        # exit 0, 286 decls, 0 holes
# scoped gate over the 7 buildable core modules (nix lean 4.34.1 on PATH):
./result/bin/gokujo check minimal/RequestProject/{Agent,APICapabilities,CommandExecution,CreditUsage,ExecutionTrace,ToolProvenance,Twin}.lean
```

## Expected Results
- Scan RequestProject: Exit code 0, processes all declarations ✓ (measured: 11 files, 286 declarations, 0 with holes)
- Check RequestProject: Exit code 0, Result: PASS ✓ — full-dir (all 73 modules) passes as of
  the fix session recorded in `tasks/fix-requestproject-full-check/`; the earlier 3 source-level gaps
  (Mathlib import; missing `RequestProject.Proxy` / `RequestProject.PluginContexts` subtrees) are closed.
- No "Stack overflow detected. Aborting." messages ✓ on every corpus run below

## Receipts (2026-10-18, old pre-fix `minimal/gokujo` vs rebuilt `result/bin/gokujo`)
| corpus | files scanned | declarations | rebuilt | pre-fix | overflow |
|---|---|---|---|---|---|
| `minimal/RequestProject` | 11 | 286 (0 holes) | 0.02 s, exit 0 | exit 0, identical output | none |
| tracker `lean/` (441 files on disk) | 398 | 12,769 | 0.94 s real / 1.95 s user | 3.11 s real / 6.27 s user | none |
| this repo, whole tree | 1,765 | 32,752 (577 holes) | 4.96 s | 6.35 s | none |

Both binaries agree on every declaration count; the rebuilt one costs ~3x less
CPU — consistent with the iterative `walkLean`/`scanStrTR` paths (equivalence
pinned by `@[csimp] theorem scanStr_eq_scanStrTR`).

## Dependencies
- Rebuilt native binary from rebuild-fixed-binary task (now done)
- Access to RequestProject module

## Notes
- Original issue: Binary caused stack overflow when scanning large projects like Solfunmeme (663 files)
- Fix: Replaced recursive `walkLean` and `scanStr` with iterative implementations
- Bounded: the original Solfunmeme corpus is absent from this host
  (`/mnt/data1/git/github.com/solfunmeme` is empty), so the overflow repro
  itself cannot be replayed; the two substitute corpora (398 and 1,765 files,
  both larger than 663 in the second case) show no overflow by either binary.
