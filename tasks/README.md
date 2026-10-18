# lean-worker Tasks

## Worktree Overview

This directory contains task documentation for the lean-worker repository.

### Worktrees

| Branch | Commit | Status |
|--------|--------|--------|
| `main` | `08a35ab` | Main development |
| `integration/vaciu-merge` | `ee86fa3` | Vaciu PRs + Aleph Cloud removal merged |
| `feature/all-worker-bindings` | `8f7c17d` | Current working branch |
| `agent/bone-proof-loop-close` | `501ffa1` | Frontend component conversion |
| `agent/buffy-p2p-knowledge-20261001` | `3133d10` | Buffy twin formalization |
| `agent/freebuff-twin` | `974639c` | FreebuffTwin verification |
| `agent/p2p-proving-bootstrap` | `da6c993` | P2P proving loop |
| `stash-0` | `f606fc9` | Stash→branch conversion |
| `stash-1` | `fe0c7ad` | Stash→branch conversion |
| `stash-2` | `4a11965` | Stash→branch conversion |
| `stash-3` | `a96a09a` | Stash→branch conversion |

### Integration Tasks

- [x] P2P proving bootstrap - Wire kant rooms + control mesh
- [x] FreebuffTwin documentation - Platform matrix, identity formalization
- [x] Context systems - Pipelight, Nora, Forgejo plugin contexts
- [x] Stash→branch conversion (`stash-0`..`stash-3` pushed to origin)

### Lean-Worker Fix Tasks

- [x] Rebuilt fixed native binary (`minimal/gokujo`, iterative `walkLean` + `scanStrTR`)
- [x] VerifiedRunner proof theorem fixes (`minimal/lean_worker_caller_combined.lean`)
- [x] Command equivalence verification (13 verifiedCaller theorems + registry theorems)
- [x] CI/CD integration (`.github/workflows/lean.yml` fix-verification step merged to `integration/vaciu-merge`)
- [x] Full-project testing (Solfunmeme-scale scan with rebuilt binary)
- [x] Documentation updates (README, N00B_GUIDE, BREAK_ROOM)

### Related Tasks

See `../pastebin-worktrees.md` for cross-repo integration tasks.
