# Makefile — go-live org
# One task = one worktree = one branch: $REPO_ROOT/worktrees/golive-org

REPO_ROOT := $(shell git rev-parse --show-toplevel)
WORKROOT  := $(REPO_ROOT)/worktrees/golive-org
SERVICES  := $(WORKROOT)/services
CLI       := $(WORKROOT)/tools/golive/cli.py
CONF      := $(WORKROOT)/config

.PHONY: help local systemd cloudflare sync peers baseline users timeline follow \
	notif logs commands status telemetry errors plan deploy

help: ## show targets
	@grep -E '^[a-z_-]+:.*?## ' $(MAKEFILE_LIST) | awk 'BEGIN {FS = ":.*?## "}; {printf "  %-16s %s\n", $$1, $$2}'

local: ## start API + nginx (userspace)
	@echo "starting API on port 8099"
	@$(CLI) local --port 8099

systemd: ## start systemd/ngix.service (port 9000, no home access)
	@echo "starting systemd/ngix.service"
	@$(CLI) systemd --conf $(CONF)/ngix.service

cloudflare: ## push api + config to Cloudflare
	@echo "deploying to Cloudflare"
	@$(CLI) cloudflare --conf $(CONF)/cloudflare.yml

sync: ## bidirectional Cloudflare <-> systemd
	@echo "syncing Cloudflare <-> systemd"
	@$(CLI) sync

peers: ## Cloudflare <-> Cloudflare peer sync
	@echo "syncing Cloudflare peers"
	@$(CLI) peers --sync

baseline: ## unauthenticated public API baseline
	@echo "recording unauthenticated baseline"
	@$(CLI) baseline

users-loggedin: ## authenticated user readings + timeline watch
	@echo "recording authenticated readings"
	@$(CLI) users --loggedin

timeline: ## watch logged-in timeline
	@echo "watching timeline"
	@$(CLI) timeline --loggedin

follow: ## following-count monitor
	@echo "monitoring following count"
	@$(CLI) follow

notif: ## push notifications attempt
	@echo "attempting push notifications"
	@$(CLI) notif

logs: ## show logs
	@cat $(WORKROOT)/logs/current.log 2>/dev/null || echo "no logs yet"

commands: ## show last commands run
	@cat $(WORKROOT)/logs/commands.log 2>/dev/null || echo "no command log yet"

status: ## show deployment status
	@echo "local:   $(shell ss -tlnp 2>/dev/null | grep 8099 || echo down)"
	@echo "systemd: $(shell systemctl is-active ngix 2>/dev/null || echo down)"
	@echo "cloudflare: $(shell curl -s -o /dev/null -w '%{http_code}' https://solana.solfunmeme.com/golive/agent/golive-org/command || echo down)"

telemetry: ## show telemetry
	@cat $(WORKROOT)/telemetry/summary.json 2>/dev/null || echo "no telemetry yet"

errors: ## show errors
	@cat $(WORKROOT)/logs/errors.log 2>/dev/null || echo "no errors yet"

plan: ## show planner
	@cat $(WORKROOT)/plan.md 2>/dev/null || echo "no planner yet"

deploy: ## show deployment output
	@cat $(WORKROOT)/deploy.log 2>/dev/null || echo "no deploy log yet"

# convenience: everything
all: help local systemd cloudflare sync peers baseline users-loggedin follow notif
