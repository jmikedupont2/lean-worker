# Task: Documentation Updates

- **Tags:** docs

**Status:** pending
**Project:** lean-worker
**Priority:** P2

## Description
Update project documentation with findings from the verifiedRunner proof fixes and the stash→branch conversion. Refresh README, N00B_GUIDE, BREAK_ROOM, and related docs with the current state of the lean-worker work.

## Context
The lean-worker repo has documentation that needs updating to reflect the fixed verification theorems, the task-tracker integration, and the current state of the worktree branches.

## Steps
1. [x] Documented verification findings in task SYSTEM.md files
2. [ ] Update README.md with current status and relevant commands
3. [ ] Update N00B_GUIDE.md with verifiedRunner theorem instructions
4. [ ] Update BREAK_ROOM.md for the stash→branch conversion outcomes
5. [ ] Update any other docs mentioning the old recursive implementation
6. [ ] Verify all links and code examples still work

## Commands
```bash
# Update docs and verify
cd /mnt/data1/time-2026/09-september/18/lean-worker
grep -r "verifiedRunner" . --include="*.md" | head -20
grep -r "stash" . --include="*.md" | head -20
```

## Verification
- All documentation examples run successfully
- README reflects current P1/P2 status of tasks
- Code examples in docs match the actual fixed binary behavior
- No references to old recursive implementation without noting the fix

## Dependencies
- Completed rebuild-fixed-binary and full-project-testing tasks
- Findings from full project testing

## Notes
- Part of the lean-worker project workflow
- Documentation should always stay in sync with the code and CI status
- Consider adding a status badge or task list summary

## Verified Findings (2026-10-17)
- `minimal/lean_worker_caller_combined.lean`: 13 verifiedRunner theorems fixed; registry theorems (`callerRegistry_allWellFormed`, `callerRegistry_has_verified_callers`, `find_lean_worker_callers`, `find_unknown_callers`) fixed to match the actual 13-entry model.
- `minimal/Gokujo.lean`: recursive `scanStr`/`walkLean` replaced with iterative `scanStrTR`/`walkLeanTR` (Solfunmeme-scale 663-file scans).
- Native binary `minimal/gokujo` rebuilt (4,349,432 bytes, ELF 64-bit).
- `flake.nix` uses local source; `github:mfng/gokujo` placeholder input is a 404 and must not be used for `nix build` here.
- `tasks/README.md` now indexes all 7 tasks + worktree overview.
