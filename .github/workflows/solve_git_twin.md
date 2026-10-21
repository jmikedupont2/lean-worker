# solve_git_twin — GitHub twin solver for lean-worker

The `jmikedupont2/lean-worker` repo wires `src/GokujoGitLayer.lean` into its
GitHub Actions CI via `.github/workflows/lean.yml`. The twin solver plays the
same role for the GitHub-facing side of that model:

1. Watches the branch (`main`) for `lean` / `verify` / `check` workflow runs.
2. Verifies the Lean twin on the same gate the CI uses (`gokujo check`).
3. Posts a signed AES-256-GCM relay envelope so the result is gossiped like
   agent-a / agent-b results.

## Files

- `solve_git_twin.mjs` — the end-to-end solver.
- `solve_git_twin.yml` — the GitHub Actions workflow that calls it.
- `solve_git_twin.md` — this document.

## Env

`GH_TOKEN`, `GH_REPO`, `BRANCH`, `RELAY`, `RELAY_ROOM`, `SALT`, `NODE_ID`.

## Relay envelope

The payload is encrypted with AES-256-GCM; the key is
`SHA256('gh-twin:' + SALT)`, the IV is 12 random bytes.
