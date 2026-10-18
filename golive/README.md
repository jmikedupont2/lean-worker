# go-live (golive.org)

One task = one worktree = one branch. Work lives in
`/root/projects/twitterstorm/worktrees/golive-org` on branch
`agent/golive-org`. Never edit in the main checkout.

## Release (20-line cap)
- repo    : $REPO_ROOT/worktrees/golive-org
- branch  : agent/golive-org
- site    : https://solana.solfunmeme.com/golive/agent/golive-org/command
- path    : $REPO_ROOT/worktrees/golive-org
- tools   : sops (env encryption), nginx local -> systemd -> Cloudflare
- data    : logs/telemetry/errors synced Cloudflare <-> systemd <-> peers

## Dashboard
Open https://solana.solfunmeme.com/golive/agent/golive-org
numbered buttons: logs, commands, plan, deploy, sync, status,
telemetry, errors.

## Run
- make help / make local / make systemd / make cloudflare / make sync / make peers
- python3 tools/golive/cli.py --help

## Guarantee
No tokens or secrets in files or env dumps; all wrapped in the API server
and Cloudflare.
