#!/usr/bin/env python3
"""golive CLI — drive the go-live org deployment from the terminal."""
import argparse, json, os, sys

REPO = os.path.expanduser("~/projects/twitterstorm")
WORK = os.path.join(REPO, "worktrees", "golive-org")
CONF = os.path.join(WORK, "config")

def sh(cmd):
    print(f"$ {cmd}")
    return 0

def cmd_local(args):
    print("local userspace API on port", args.port or 8099)
    return sh(f"node {os.path.join(WORK, 'services', 'api.js')} --port {args.port or 8099}")

def cmd_systemd(args):
    print("starting systemd/ngix.service (port 9000, no home access)")
    return sh(f"sudo systemctl start ngix.service")

def cmd_cloudflare(args):
    print("deploying to Cloudflare")
    return sh(f"cloudflare deploy --config {args.conf or os.path.join(CONF, 'cloudflare.yml')}")

def cmd_sync(args):
    print("bidirectional sync Cloudflare <-> systemd")
    return sh(f"{WORK}/bin/sync")

def cmd_peers(args):
    print("Cloudflare <-> Cloudflare peer sync" + (" --sync" if args.sync else ""))
    return sh(f"{WORK}/bin/peer-sync --sync {args.sync}")

def cmd_baseline(args):
    print("recording unauthenticated public API baseline")
    return sh(f"{WORK}/bin/baseline")

def cmd_users(args):
    print("authenticated readings + timeline watch" + (" --loggedin" if args.loggedin else ""))
    return sh(f"{WORK}/bin/users --loggedin {args.loggedin}")

def cmd_timeline(args):
    print("watching logged-in timeline")
    return sh(f"{WORK}/bin/timeline --loggedin")

def cmd_follow(args):
    print("monitoring following count")
    return sh(f"{WORK}/bin/follow")

def cmd_notif(args):
    print("attempting push notifications")
    return sh(f"{WORK}/bin/notif")

def cmd_logs(args):
    p = os.path.join(WORK, "logs", "current.log")
    print(open(p).read() if os.path.exists(p) else "no logs yet")
    return 0

def cmd_commands(args):
    p = os.path.join(WORK, "logs", "commands.log")
    print(open(p).read() if os.path.exists(p) else "no command log yet")
    return 0

def cmd_status(args):
    print("local   :", "up:8099" if os.path.exists("/tmp/golive-8099") else "down")
    print("systemd :", "up" if os.path.exists("/tmp/golive-systemd") else "down")
    print("cloudflare:", "up" if os.path.exists("/tmp/golive-cf") else "down")
    return 0

def cmd_telemetry(args):
    p = os.path.join(WORK, "telemetry", "summary.json")
    print(open(p).read() if os.path.exists(p) else "no telemetry yet")
    return 0

def cmd_errors(args):
    p = os.path.join(WORK, "logs", "errors.log")
    print(open(p).read() if os.path.exists(p) else "no errors yet")
    return 0

def cmd_plan(args):
    p = os.path.join(WORK, "plan.md")
    print(open(p).read() if os.path.exists(p) else "no planner yet")
    return 0

def cmd_deploy(args):
    p = os.path.join(WORK, "deploy.log")
    print(open(p).read() if os.path.exists(p) else "no deploy log yet")
    return 0

def main():
    ap = argparse.ArgumentParser(prog="golive")
    sub = ap.add_subparsers(dest="cmd", required=True)

    p = sub.add_parser("local"); p.add_argument("--port", type=int); p.set_defaults(func=cmd_local)
    p = sub.add_parser("systemd"); p.set_defaults(func=cmd_systemd)
    p = sub.add_parser("cloudflare"); p.add_argument("--conf"); p.set_defaults(func=cmd_cloudflare)
    p = sub.add_parser("sync"); p.set_defaults(func=cmd_sync)
    p = sub.add_parser("peers"); p.add_argument("--sync", action="store_true"); p.set_defaults(func=cmd_peers)
    p = sub.add_parser("baseline"); p.set_defaults(func=cmd_baseline)
    p = sub.add_parser("users"); p.add_argument("--loggedin", action="store_true"); p.set_defaults(func=cmd_users)
    p = sub.add_parser("timeline"); p.add_argument("--loggedin", action="store_true"); p.set_defaults(func=cmd_timeline)
    p = sub.add_parser("follow"); p.set_defaults(func=cmd_follow)
    p = sub.add_parser("notif"); p.set_defaults(func=cmd_notif)
    p = sub.add_parser("logs"); p.set_defaults(func=cmd_logs)
    p = sub.add_parser("commands"); p.set_defaults(func=cmd_commands)
    p = sub.add_parser("status"); p.set_defaults(func=cmd_status)
    p = sub.add_parser("telemetry"); p.set_defaults(func=cmd_telemetry)
    p = sub.add_parser("errors"); p.set_defaults(func=cmd_errors)
    p = sub.add_parser("plan"); p.set_defaults(func=cmd_plan)
    p = sub.add_parser("deploy"); p.set_defaults(func=cmd_deploy)

    args = ap.parse_args()
    sys.exit(args.func(args))

if __name__ == "__main__":
    main()
