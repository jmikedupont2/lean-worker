# Task: Documentation Updates

**Status:** pending
**Project:** lean-worker
**Priority:** P2

## Description
Update project documentation with findings from the verifiedRunner proof fixes and the stash→branch conversion. Refresh README, N00B_GUIDE, BREAK_ROOM, and related docs with the current state of the lean-worker work.

## Context
The lean-worker repo has documentation that needs updating to reflect the fixed verification theorems, the task-tracker integration, and the current state of the worktree branches.

## Steps
1. [ ] Update README.md with current status and relevant commands
2. [ ] Update N00B_GUIDE.md with verifiedRunner theorem instructions
3. [ ] Update BREAK_ROOM.md for the stash→branch conversion outcomes
4. [ ] Update any other docs mentioning the old recursive implementation
5. [ ] Verify all links and code examples still work

## Commands
```bash
# Update docs and verify
cd /home/mdupont/projects/lean-worker
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
