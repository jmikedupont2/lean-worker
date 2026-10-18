# go-live release — 2026-10-16

- repo    : /root/projects/twitterstorm/worktrees/golive-org
- branch  : agent/golive-org (fresh worktree, never committed to main)
- site    : https://solana.solfunmeme.com/golive/agent/golive-org/command
- path    : $REPO_ROOT/worktrees/golive-org
- tools   : sops (env encryption), nginx local -> systemd -> Cloudflare
- data    : logs/telemetry/errors synced Cloudflare <-> systemd <-> peers

buttons : / (dashboard) /logs /commands /plan /deploy /sync /status /telemetry /errors
port    : 8099 (nginx), 9000 (systemd), cf :443

make    : make help
cli     : python3 tools/golive/cli.py --help
