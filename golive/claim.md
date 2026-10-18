# claim.md — go-live org

## Worktree & branch
- worktree: `$REPO_ROOT/worktrees/golive-org`
- branch: `agent/golive-org` (fresh, committed only inside the worktree)
- parent: `/root/projects/twitterstorm`
- tracker: `/root/projects/twitterstorm/tracker` (not written; use the worktree)

## Release targets
1. sops-encrypted env at every layer (no tokens in files or env dumps)
2. local userspace (nginx) -> systemd (`systemd/ngix.service`) -> Cloudflare
3. Cloudflare front, systemd blocked from user home (`ReadonlyPaths`)
4. bidirectional sync: Cloudflare <-> systemd (logs, telemetry, errors)
5. Cloudflare <-> Cloudflare peer sync
6. unauthenticated public API baseline + authenticated user readings
7. logged-in timeline watch + following-count monitor
8. push notifications attempted
9. full error/log/telemetry capture shared to systemd
10. clickable numbered buttons on the front page with log view
11. Cloudflare deployment planner (planner.md)
12. CLI (`tools/golive/cli.py`) + Makefile for all commands
13. GUI->proof tested; CLI to drive the GUI headlessly

## Services
- solana.solfunmeme.com/golive/agent/<branchname>/command
- nginx local on 8099; systemd on 9000; Cloudflare HTTPS
- all tokens wrapped in the api server + Cloudflare; nothing exposed in files

## Status
- report created (20-line cap)
- claim.md staged
- to do: sops key setup, nginx/systemd/Cloudflare config, data sync pipeline, CLI+Makefile, GUI->proof test
