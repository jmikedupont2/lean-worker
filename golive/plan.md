# planner — cloudflare deployment

Stages:
1. sops key + encrypted env for each tier (local, systemd, Cloudflare)
2. local userspace: API server + nginx on port 8099
3. systemd: systemd/ngix.service (port 9000), no access to user home
4. Cloudflare: edge proxy + API deploy, HTTPS, no token exposure
5. Bidirectional sync tool (logs/telemetry/errors): cloudflare -> systemd
6. Cloudflare <-> Cloudflare peer sync (watch list + following count)
7. Baselines: unauthenticated public API, then authenticated user reads/writes
8. Timeline watch + following-count monitor; push notifications attempt
9. Error capture: all logs, telemetry, results -> systemd service
10. Dashboard URL shareable; numbered buttons + CLI + Makefile

Makefile targets (in project root):
- make run-local        : start API + nginx (userspace)
- make run-systemd      : start systemd/ngix.service
- make deploy-cloudflare: push api + config to Cloudflare
- make sync-cloudflare  : bidirectional Cloudflare <-> systemd sync
- make sync-peers       : Cloudflare <-> Cloudflare peer sync
- make baseline         : unauthenticated baseline dump
- make users-loggedin   : authenticated readings + timeline watch
- make monitor-follow   : following-count monitor
- make push-notif       : push notifications attempt
- make logs/commands/status/telemetry/errors : view sections
- make plan/deploy      : planner + deploy outputs
- make help

CLI:
- python3 tools/golive/cli.py --help
- cmds: local, systemd, cloudflare, sync, peers, baseline, users, timeline,
       follow, notif, logs, commands, status, telemetry, errors, plan, deploy
