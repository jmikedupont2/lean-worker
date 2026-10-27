# Task Queue — lean-worker tracker

Runnable list for the task-runner. Ordered by priority. Every entry was
verified against live repo state on 2026-10-24; sources cited per task.

Conventions (`tracker/AGENTS.md`): one task = one worktree = one branch
(`bash scripts/new-task.sh <name>`), never work in the main checkout, and each
task states the exit-0 command that proves it done.

---

## Run log — 2026-10-27

- **DONE 2 (resolve-pr-15-conflict):** `otc-desk-relay-mailbox` rebased onto
  `origin/integration/vaciu-merge` (docs resolved to PR refresh; `.gitignore`
  union), force-pushed with lease → `MERGEABLE`. PR still open.
- **DONE 3 (resolve-pr-16-conflict):** decision = close. `295e7d7` has an
  identical patch-id to `93ae9a6` (already on `main` via #13); PR #16 closed
  as duplicate with explanation.
- **DONE 4 (review-and-merge-pr-14):** reviewed CHECK-gate wiring + refless
  mode; rebuilt checker under nixpkgs `lean4` (no elan) and ran the RT-9
  suite: full pass=8 fail=0, refless pass=7 fail=0. Merged → `5b32f48` on
  `main` (PR base had been switched from integration).
- **NEW closure — PR #17 (Feature/cleanup):** merged 2026-10-27 into
  `integration/vaciu-merge` (`cf69dd7`); removes the embedded copies plus
  compiled artifacts (`minimal/gokujo`, `minimal/test`, `result`,
  locate-lean-worker dumps).
- **DONE 5 (reconcile-local-main):** the 3 local-only commits are worth
  nothing at tips (gokujo binary + source byte-identical on `main`; docs
  stale; flake fix superseded by `ad61696`). Tagged
  `backup/main-diverged-20261027`, aligned local `main` to `origin/main`
  (`5b32f48`). Note `origin/main` and `mi/main` are themselves diverged
  (10 vs 53) — fork/upstream sync is a separate decision.
- **DONE 9 (remove-broken-letta-worktrees):** extended — ALL embedded worktree
  copies (`worktrees/` 1628, `explore/` 674, `.letta/` 590 files) verified as
  duplicate content, then untracked in `9a2e82e` with `.gitignore` guards for
  the paths and compiled binaries. `git worktree prune` had nothing stale.
- **DONE 10 (sync-tasks-readme-branch-table):** regenerated from live
  `git rev-parse` state.

---

## P0

### 1. gokujo-mcp-stdio-execution
- **Source:** `tasks/gokujo-mcp-stdio-execution/SYSTEM.md` (status: open, P0)
- **Do:** Execute the gokujo MCP stdio path end-to-end and close the task.
- **Verify:** `cd minimal && lake build` exits 0, then the stdio round-trip
  completes against the built binary.

---

## P1

### 2. resolve-pr-15-conflict
- **Source:** PR #15 `otc-desk-relay-mailbox` → `integration/vaciu-merge`,
  GitHub reports `mergeable: CONFLICTING`.
- **Do:** Rebase onto `origin/integration/vaciu-merge`, resolve conflicts in
  the docs/.gitignore files the PR touches, force-push the branch.
- **Verify:** `gh pr view 15 --json mergeable -q .mergeable` → `MERGEABLE`.

### 3. resolve-pr-16-conflict
- **Source:** PR #16 `letta/job-verifier-pr25` → `integration/vaciu-merge`,
  GitHub reports `mergeable: CONFLICTING`.
- **Do:** Rebase onto the base and resolve conflicts. **Decide first** whether
  to land this original commit (`295e7d7`) or cherry-pick the rebased twin
  `93ae9a6` already merged to `main` via #13 — they implement the same CHECK
  gate and landing both duplicates it.
- **Verify:** `gh pr view 16 --json mergeable -q .mergeable` → `MERGEABLE`,
  and the JobVerifier regression suite passes 8/8.

### 4. review-and-merge-pr-14
- **Source:** PR #14 `letta/wire-job-verifier-bone-worker`, open since
  2026-10-22, `mergeable: MERGEABLE` — the only conflict-free PR.
- **Do:** Review the bone-worker CHECK-gate wiring, run the verification, merge.
- **Verify:** PR #14 shows `MERGED`; `cd minimal && lake build` exits 0.

### 5. reconcile-local-main
- **Source:** local `main` (3 commits) vs `origin/main` (8 commits) have
  diverged — a plain push is rejected; forcing would discard 8 remote commits.
- **Do:** Rebase local `main` onto `origin/main` (never force-push), keeping the
  remote's 8 commits. Note all 3 local-only commits are already patch-present in
  `integration/vaciu-merge`, so if nothing is gained, document and abandon.
- **Verify:** `git merge-base --is-ancestor origin/main main` exits 0;
  `git push origin main` fast-forwards without `--force`.

### 6. command-equivalence-verification
- **Source:** `tasks/command-equivalence-verification/SYSTEM.md`
  (status: in_progress, P1).
- **Do:** Finish the 13 verifiedCaller theorems + registry theorems. Note the
  file `minimal/lean_worker_caller_combined.lean` is tracked as `MM` (differs
  from both index and HEAD) — settle that state.
- **Verify:** `lean minimal/lean_worker_caller_combined.lean` exits 0 with no
  errors.

### 7. gokujo-protocol-registry-overhaul
- **Source:** `tasks/gokujo-protocol-registry-overhaul/SYSTEM.md`
  (status: open, P1).
- **Do:** Overhaul the protocol registry per the task's SYSTEM.md scope.
- **Verify:** `cd minimal && lake build` exits 0 and the registry theorems pass.

### 8. close-bone-proof-loop
- **Source:** `tracker/AGENTS.md` Priority 1; `tracker/current-task.md`
  (in_progress, last updated 2026-09-30 — stale by ~3.5 weeks).
- **Do:** Watch task-runner `bone-*` summaries, re-emit offers, flip
  `results.jsonl` to `proved`.
- **Verify:** `node minimal/scripts/failed-to-taskrunner.mjs` dry-run reports
  bridge stats with no failures.

---

## P2

### 9. remove-broken-letta-worktrees
- **Source:** `SUMMARY_OF_WORK.md` "Stale Worktrees (Cleanup Needed)";
  verified 2026-10-24 — `.letta/worktrees/merge-vaciu-prs/` and
  `.letta/worktrees/microgokujo-interfaces/` have **no `.git` file** (broken
  gitdir pointers).
- **Do:** `git worktree prune` to clear dead registrations, then delete the two
  orphaned directories. Check for uncommitted work inside before removing.
- **Verify:** `git worktree list` no longer references either path;
  `git status --porcelain` stays clean.

### 10. sync-tasks-readme-branch-table
- **Source:** `tasks/README.md` worktree table lists branches/commits that no
  longer match reality (e.g. `feature/all-worker-bindings` is now
  `feature/all-worker-bindings-local`; `integration/vaciu-merge` moved past
  `ee86fa3`).
- **Do:** Regenerate the branch/commit/status table from live git state.
- **Verify:** every `git rev-parse <branch>` in the table resolves and matches.

### 11. gokujo-git-adapter-completion
- **Source:** `tracker/tasks/INDEX.md` (in-progress, stale);
  `minimal/TASK_LIST.md` In Progress section.
- **Do:** Complete the truncated `gokujo_git_adapter.py`:
  `GitHubManager.pr_merge` (started, incomplete), issue management, release
  management, workflow dispatch, plus the `_run_gh` and `_parse_pr_response`
  helpers.
- **Verify:** `python3 gokujo_git_adapter.py --list-tools` runs and all 16
  tools dispatch without `NotImplementedError`.

### 12. desk-server-deploy
- **Source:** `tracker/tasks/INDEX.md` (proposed).
- **Do:** Deploy `DeskServer/desk-relay.mjs` as a managed service (Priority 2 in
  `tracker/AGENTS.md` — Desk/DMZ module completion).
- **Verify:** the service is `active` under systemd and the relay answers a
  health request.

### 13. shared-lake-cache-tooling
- **Source:** `tracker/tasks/INDEX.md` (in-progress) — README pointer landed,
  tooling lives in aristotle-manager.
- **Do:** Finish the shared lake-cache tooling hand-off (see
  `SHARED_LAKE_CACHE.md` for the command surface).
- **Verify:** `aristotle-manager cache status <PROJECT>` reports the project
  linked into the shared store.

### 14. cicd-integration
- **Source:** `tasks/cicd-integration/SYSTEM.md` (pending, P2).
- **Do:** Wire the remaining CI/CD integration steps.
- **Verify:** status checks show successful build and test on the PR.

### 15. documentation-updates
- **Source:** `tasks/documentation-updates/SYSTEM.md` (pending, P2).
- **Do:** Bring `README.md` in line with current P1/P2 status and commands.
- **Verify:** README reflects the current task statuses in this queue.

### 16. gokujo-adapter-composability
- **Source:** `tasks/gokujo-adapter-composability/SYSTEM.md` (open, P2).
- **Do:** Close the adapter composability task.
- **Verify:** `cd minimal && lake build` exits 0 and the adapter tests pass.

---

## Deferred / decided-not-to-do

- **Push local `main` as-is** — declined 2026-10-24: requires `--force` and
  would discard 8 remote commits; all 3 local-only commits are already
  patch-present in the default branch. Reconcile via task 5 instead.
