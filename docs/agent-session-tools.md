# Agent session & usage tools in the lean-worker devShell

`flake.nix` pulls `github:numtide/llm-agents.nix` as the `llm-agents-src` input
and puts six session/usage CLIs into `devShells.default.buildInputs`, so
`nix develop` gives you analysis tools alongside `lean4`/`git`/`jq`:

```bash
nix develop            # then:
agentsview --help      # local-first viewer + analytics for agent sessions
ccusage daily          # token usage & cost from local agent CLI data
cpa-usage-keeper -v    # CLIProxyAPI usage tracker + dashboard (needs CPA_*)
entire --help          # capture agent sessions, link them to code changes
mindwalk --help        # replay a session on a 3D map of the codebase
tokscale models        # CLI/TUI token-usage analytics
```

Why this input is configured the way it is (copied from
`~/projects/system-manager/flake.nix`, where the same note was written first):
**nixpkgs is deliberately not followed**. llm-agents.nix pins its own
nixpkgs-unstable and publishes daily builds to `https://cache.numtide.com`;
following ours would rebuild the Go/npm tooling from source and miss that cache.

Read-only notes:

- `mindwalk` takes `--pi-dir`, so it can read the `pi` session JSONL that the
  capture pipeline tails into `logs/capture-*/agents/*.tail`.
- `cpa-usage-keeper` exits with `CPA_BASE_URL is required` on a host with no
  CLIProxyAPI — that is expected, not a broken install.
- Full comparison of the six tools: `~/DOCS/AGENT_SESSION_TOOLING.md`.
