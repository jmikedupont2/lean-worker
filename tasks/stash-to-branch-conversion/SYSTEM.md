# Task: Stash to Branch Conversion

**Status:** done
**Project:** lean-worker
**Priority:** P1

## Description
Convert the four git stashes (`stash@{0}`..`stash@{3}`) into permanent branches (`stash-0`..`stash-3`) on the shared origin repository, ensuring the stash content is fully embodied in named branches and the working tree is clean.

## Context
- Stash `stash@{0}` → WIP on `agent/bone-proof-loop-close` (390526f): `minimal/GCP/Types.lean` abbrev fixes + `minimal/Twin.lean` edits
- Stash `stash@{1}` → WIP on `fix-gcp-build` (26316a8): `minimal/lakefile.toml` rename `Minimal`→`RequestProject`
- Stash `stash@{2}` → WIP on `agent/bone-proof-loop-close` (501ffa1): `minimal/lakefile.toml` fix
- Stash `stash@{3}` → `On fix-gcp-build: pre-rebase` untracked files (tree has 3 parents: db5dd17, e919b59, 8629477)

## Branch Tips

| Branch | Tip SHA | WIP origin |
|--------|---------|------------|
| `stash-0` | f606fc9 | WIP on agent/bone-proof-loop-close: 390526f |
| `stash-1` | fe0c7ad | WIP on fix-gcp-build: 26316a8 |
| `stash-2` | 4a11965 | WIP on agent/bone-proof-loop-close: 501ffa1 |
| `stash-3` | a96a09a | On fix-gcp-build: pre-rebase: untracked files |

## Steps
1. [x] Inspect each stash's content and commit context
2. [x] Create branches `stash-0`..`stash-3` from the stash tips
3. [x] Push all four branches to the shared origin repository
4. [x] Verify each branch exists on the remote (`git ls-remote origin refs/heads/stash-*`)
5. [x] Confirm `git stash list` returns empty in the working tree
6. [x] Write a memo into `gitplan.org` documenting the conversion and branch table

## Verification
- `git branch -v` shows all four branches locally
- `git ls-remote origin refs/heads/stash-*` lists all four on the shared repo
- `git stash list` in the working tree returns empty
- `git show-ref` shows the branches at their tip SHAs
- Memo in `gitplan.org` documents the conversion accurately

## Files Changed
- No source files were edited during the conversion; the git history was updated only.
- Memo written to `/home/mdupont/05/28/gitplan.org` (which is a symlink to `~/gitplan.org`).

## Dependencies
- Access to the shared origin repository
- Read permission on the shared repo's packed-refs

## Notes
- The `refs/stash` entry in the working tree's `packed-refs` was a leftover from the original `stash list` and is inert (no applied working-tree state). It no longer affects the working tree, branches, or remote history.
