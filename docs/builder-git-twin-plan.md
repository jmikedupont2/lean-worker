# Builder + git_twin integration — plan and what was done

## 1. What "private fork" refers to

The repo's git **origin is public**: `origin = https://github.com/jmikedupont2/lean-worker.git`
(see `.git/config`). There is **no private fork configured** in the repo itself.

The "private fork" references came from the *documentation* file
`githubtwin.md` (and `solve_git_twin.md`), which name a **separate twin
repository**: `https://github.com/meta-introspector/lean-worker-gh-twin`
(the GitHub twin for the agent's claims/relay protocol).

So:

- `origin` = public `jmikedupont2/lean-worker.git` (this repo) — **no private fork in config**.
- `githubtwin.md` / `solve_git_twin.*` = docs that point at a *separate* private twin repo
  for the GitHub/relay twin model.

No private-fork refs were removed from the docs, but the repo itself has no private fork.

## 2. What was done — native `gokujo` builder + GitHub Actions + git_twin

### 2a. `minimal/Builder.lean` (new)
Builder module with the native `gokujo` cache-and-reuse strategy:

- `gokujoExe` — the self-contained `gokujo` binary.
- `cacheKey` — a cache key that hashes the source files that must compile
  (`Gokujo.lean`, `GokujoMain.lean`, `Builder.lean`, `.github/workflows/lean.yml`).
- `bootstrapCmd` — `gokujo bootstrap -o gokujo --backend bundled`.
- `builderGokujoBuildStep` / `builderGokujoUseStep` — the GitHub Actions steps
  that build native `gokujo` once, cache it, and reuse the cached binary.
- `githubWorkflow` — the generated GitHub Actions workflow for the **builder**
  (`Lean 4 Builder + git_twin`): matrix backends `[bundled, system, elan, lake, nix]`,
  an `actions/cache` step keyed on the builder's source hash, a `make -C minimal builder`
  build step, and a `solve_git_twin` step that drives the git_twin end to end.

### 2b. `minimal/GokujoInfra.lean` (modified)
Added `builderGithubWorkflow` — the GitHub Actions workflow content generated
by the `Infra` namespace that wires `solve_git_twin` into the builder CI
(builds `gokujo`, caches the binary, runs `solve_git_twin`, publishes twin status).

### 2c. GitHub Actions: `solve_git_twin` workflow (new)
- `.github/workflows/solve_git_twin.mjs` — the end-to-end twin solver.
- `.github/workflows/solve_git_twin.yml` — the GitHub Actions workflow that
  runs the solver, with the env vars (`GH_TOKEN`, `GH_REPO`, `BRANCH`,
  `RELAY`, `RELAY_ROOM`, `SALT`, `NODE_ID`).
- `.github/workflows/solve_git_twin.md` — this workflow's doc.

### 2d. `tools/gokujo/Gokujo.lean` (modified)
Updated to reflect the builder configuration and the new GitHub Actions
workflow wiring (the existing changes already present in the working tree).

## 3. Confirmed facts

- Branch: `integration/vaciu-merge`
- HEAD: `b85edd5` — "feat: add native gokujo builder with GitHub Actions
  cache-and-reuse + git_twin" (5 files, 431 insertions).
- Remote: `https://github.com/jmikedupont2/lean-worker.git`
  (`origin`)
- Git identity: James Michael DuPont / jmikedupont2@gmail.com

## 4. Remaining — why the push/PR could not be completed here

The environment cannot reach GitHub:

```
fatal: unable to access 'https://github.com/jmikedupont2/lean-worker.git/':
  Could not resolve host: github.com
```

DNS / outbound network to `github.com` is not available in this sandbox, so:

- `git push -u origin integration/vaciu-merge` **failed** — DNS resolution timed out.
- I therefore **cannot create the PR automatically**.

## 5. Plan to finish (needs your / a reachable network)

1. From a host where `github.com` resolves, run:
   ```bash
   cd /home/mdupont/projects/lean-worker
   git push -u origin integration/vaciu-merge
   ```
2. Then create the PR from `integration/vaciu-merge` into `main`:
   ```bash
   gh pr create --title "feat: native gokujo builder + GitHub Actions cache-and-reuse + git_twin" \
     --body "$(cat docs/builder-git-twin-plan.md)"
   ```
   (or via the GitHub web UI: `https://github.com/jmikedupont2/lean-worker/pull/new/integration/vaciu-merge`)
3. After the PR is up, `gh pr checks` will show the GitHub Actions CI running
   the new builder + `solve_git_twin` workflow.

## 6. Untouched by this work (for context)

- The merge artifacts: ~575 untracked files and ~1053 modified files under
  `explore/*`, `worktrees/*`, `minimal/*` (from the `integration/vaciu-merge`
  merge). Those are pre-existing merge state, **not** part of this change.
- `githubtwin.md` / `solve_git_twin.*` docs left as reference (the private-fork
  references are documented and traced to the twin repo, not this repo).
