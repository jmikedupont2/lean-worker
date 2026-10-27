# lean-worker Tasks

## Worktree Overview

This directory contains task documentation for the lean-worker repository.

### Worktrees (live, 2026-10-27)

| Branch | Commit | Status |
|--------|--------|--------|
| `main` | `5b32f48` | PR home (origin); job-verifier #13/#14 landed |
| `origin/integration/vaciu-merge` | `cf69dd7` | Default branch; cleanup PR #17 landed |
| `int-merge` | `9a2e82e` | Working line: gokujo plugin negotiation + worktree-copy untracking (unpushed) |
| `otc-desk-relay-mailbox` | `b48a71b` | PR #15 rebased onto base, MERGEABLE, awaiting merge |
| `feature/cleanup` | `4c9fe86` | Merged via PR #17 (2026-10-27) |
| `letta/wire-job-verifier-bone-worker` | `31debc0` | Merged via PR #14 (2026-10-27) |
| `letta/job-verifier-pr25` | `295e7d7` | PR #16 closed as duplicate of #13 |
| `feature/all-worker-bindings-local` | `7f3cccd` | Merged via PR #3 |
| `feature/gokujo-split-local` | `0558838` | Merged via PR #5 |
| `feature/gokujo-updates-local` | `07c5624` | Merged via PR #7 |
| `explore/minimathlib` | `69ca2c7` | Merged via PR #6 |
| `agent/p2p-proving-bootstrap` | `64e878c` | Merged via PR #8 lineage |
| `agent/freebuff-twin` | `da1081d` | Historical |

Embedded worktree copies (`worktrees/`, `explore/`, `.letta/`) were untracked
in `9a2e82e`; paths are gitignored. Old snapshot preserved at tag
`backup/main-diverged-20261027`.

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
