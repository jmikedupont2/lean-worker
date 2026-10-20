/-!
# ServiceSpec — single-source-of-truth for nginx + systemd pairs

Every service in the system-manager needs two artifacts that drift apart:

  `nginx/services.d/SERVICE.conf`   ← port, path, auth, proxy
  `modules/SERVICE.nix`            ← ExecStart, WorkingDir, Restart

This file is the single source of truth. Define a service here, then run:

    lean --run ServiceSpec.lean                      # print all rendered configs
    lean --run ServiceSpec.lean gui2proof             # render one service
    lean --run ServiceSpec.lean publish /path/to/system-manager

## Service kinds

| kind     | ExecStart pattern                   | Example          |
|----------|-------------------------------------|------------------|
| `node`   | `node ${exec} ${args}`              | gui2proof, kant  |
| `rust`   | `${exec} ${args}`                   | aristotle-mgr    |
| `python` | `python3 ${exec} ${args}`            | concept-api      |
| `lean`   | `lean ${exec} ${args}`              | lean4-repl       |
| `static` | (no ExecStart; alias + try_files)  | aristo WASM UI   |

## Design

- `services` array: one Spec per deployed service, sorted alphabetically.
- `emitNginx` / `emitSystemd`: render from one Spec.
- `renderAll`: print all configs (nginx first, then systemd).
- `publish dir`: write generated files into a system-manager checkout.
- Edit this file, run `lean --run ServiceSpec.lean`, review the output,
  then `publish` to copy into the system-manager.
-/

namespace ServiceSpec

/-! ## 1. Service specification -/

inductive Kind
  | node | rust | python | lean | static
  deriving DecidableEq, Repr, Inhabited

structure Spec where
  name           : String
  description    : String
  kind           : Kind
  workingDir     : String
  exec           : String := ""
  args           : String := ""
  port           : Nat
  path           : String
  auth           : Bool := false
  cors           : Bool := false
  websocket      : Bool := false
  proxyTimeout   : Nat := 120
  restart        : String := "always"
  restartSec     : Nat := 5
  nginxHeader    : String := ""
  nginxExtra     : String := ""
  env            : String := ""
  systemdExtra   : String := ""
  serviceConfigExtra : String := ""
  deriving Inhabited

/-! ## 2. Service database — alphabetically sorted -/

/-! ## 2. Service database — alphabetically sorted -/

def services : List Spec :=
  [
    -- Agentaps
    Spec.mk "agentaps" "Agentaps desktop workspace" .node
      "/home/mdupont/projects/agentaps" "node server.mjs" ""
      3000 "/agentaps/" false false false 60 "always" 5
      ""
      ""
      ""
      ""
      ""
    -- Aristo (static — no ExecStart, nginx alias + try_files)
    Spec.mk "aristo" "Aristotle WASM UI + API" .static
      "/mnt/data1/time-2026/05-may/07/arist/www" "" ""
      9876 "/aristo/" false true false 120 "always" 5
      "# Consolidated Aristotle nginx configuration\n# Included from solana.solfunmeme.com TLS vhost via services.d/*.conf\n#\n#   /aristo                          → static WASM UI (www/)\n#   /aristo/api/                     → aristotle-manager serve :9876\n#   /aristo/health                   → aristotle-manager health\n#   /aristo/verify                   → aristotle-manager verify endpoint\n#   /aristo/plan                     → DASP planner tile (:8888)\n#   /aristo/alias-web                → alias-web :8083\n#\n# Disabled: /aristo/gokujo/*, /aristo/gui2proof/*, /aristo/p2p/*, /aristo/file-drop/*\n#"
      "# Static WASM UI: serves www/ with SPA fallback\n"
        ++ "location ^~ /aristo/ {\n"
        ++ "    alias /mnt/data1/time-2026/05-may/07/arist/www/;\n"
        ++ "    index index.html;\n"
        ++ "    try_files $uri $uri/ /aristo/index.html;\n"
        ++ "    add_header Cache-Control \"public, max-age=300\";\n"
        ++ "    types { application/wasm wasm; }\n"
        ++ "}\n"
      ""
      ""
      ""
      ""
    -- Cloudflare Coordination
    Spec.mk "cloudflare-coordination" "Cloudflare Coordination Dashboard" .static
      "/home/mdupont/projects/twitterstorm/cloudflare" "" ""
      0 "/cloudflare/" false true false 120 "always" 5
      "# Cloudflare Coordination Dashboard — /cloudflare/\n"
        ++ "# Static site from twitterstorm/cloudflare/\n"
        ++ "access_log /var/log/nginx/cloudflare-dashboard.log combined;\n\n"
      ""
      ""
      ""
      ""
    -- Concept API
    Spec.mk "concept-api" "Concept/Value lattice API" .python
      "/home/mdupont/2026/concept-lattice-web" "concept_api.py" ""
      9999 "/concept/" false false false 120 "always" 5
      ""
      ""
      ""
      ""
      ""
    -- Control Node
    Spec.mk "control-node" "Control Node (TypeScript Worker :8808)" .node
      "/home/mdupont/projects/twitterstorm/control-node" "src/index.ts" ""
      8808 "/control-node/" false false false 60 "always" 5
      "# Control Node (Port 8808 - TypeScript Worker)\n"
      ""
      ""
      ""
      ""
    -- Forgejo
    Spec.mk "forgejo" "Forgejo git forge" .node
      "/home/mdupont/projects/forgejo" "node server.js" ""
      3000 "/forgejo/" false true false 120 "always" 5
      "# Forgejo git forge — Gitea/Forgejo subpath deployment\n"
        ++ "# Auth: Forgejo's own user/token auth governs.\n\n"
      ""
      ""
      ""
      ""
    -- Go-Live Deck
    Spec.mk "golive-deck" "Go-live control deck" .node
      "/home/mdupont/projects/twitterstorm/golive-deck" "node deck.mjs" ""
      3341 "/golive/" false true false 120 "always" 5
      "# Go-live control deck (loopback :3341). Auth is app-level.\n"
        ++ "# /health stays public for uptime probes.\n\n"
      ""
      ""
      ""
      ""
    -- Go-Live Branch Base
    Spec.mk "golive-branch-base" "Go-live branch preview base" .node
      "/home/mdupont/projects/twitterstorm/golive-branch-base" "server.mjs" ""
      38888 "/golive/branch/" false false false 60 "always" 5
      "# Go-Live Base branch — fronts the go-live server on port 38888\n"
        ++ "# URL: https://solana.solfunmeme.com/twitterstorm/golive/branchname/\n"
        ++ "# Backend: http://127.0.0.1:38888\n"
        ++ "# Internal test API only (no external dependencies)\n\n"
      ""
      ""
      ""
      ""
    -- GUI2Proof
    Spec.mk "gui2proof" "DASL GUI2Proof service (Lean's GUI-proof side)" .node
      "/mnt/data1/time-2026/05-may/07/arist" "scripts/start-gui2proof.mjs" ""
      9890 "/gui2proof/" true true false 180 "always" 5
      "# GUI2Proof control surface; the service binds only to localhost.\n"
        ++ "# EDGE-GATED: unauthenticated trigger through the vhost.\n"
        ++ "# Gated with the tracker auth_request machinery.\n\n"
      ""
      ""
      ""
      ""
    -- Kant Relay
    Spec.mk "kant-relay" "Kant ZK Rendezvous Relay" .node
      "/home/mdupont/projects/kant-zk-pastebin" "server/relay.mjs" "--port 8787 --host 127.0.0.1"
      8787 "/relay/" false true true 86400 "always" 5
      "# kant-zk relay — node twin at 127.0.0.1:8787\n"
        ++ "# PUBLIC: rooms are unguessable; access is via shared links.\n\n"
      ""
      ""
      ""
      ""
    -- Kant Pastebin
    Spec.mk "pastebin" "Kant Pastebin" .node
      "/home/mdupont/projects/kant-pastebin" "node server.mjs" ""
      8090 "/pastebin/" false true false 120 "always" 5
      "# Kant Pastebin (Port 8090)\n"
      ""
      ""
      ""
      ""
    -- SPARQL GUI
    Spec.mk "sparql-gui" "SPARQL GUI" .python
      "/home/mdupont/projects/sparql-gui" "app.py" ""
      8088 "/sparql-gui/" false true false 120 "always" 5
      ""
      ""
      ""
      ""
      ""
    -- Tracker Agents
    Spec.mk "tracker-agents" "Tracker agent control (tmux/agents :3313)" .node
      "/home/mdupont/projects/twitterstorm/tracker" "node src/agents.mjs" ""
      3313 "/tracker/agents/" true false false 60 "always" 5
      "# Tracker agent control (tmux/agents surface of :3313)\n"
        ++ "# Edge gate: session cookie OR legacy ops basic-auth pair.\n\n"
      ""
      ""
      ""
      ""
    -- Tracker Dashboards
    Spec.mk "tracker-dashboards" "Tracker dashboards (KPI :3313, ladder :3340)" .node
      "/home/mdupont/projects/twitterstorm/tracker" "node src/dashboards.mjs" ""
      3313 "/tracker/" true true false 120 "always" 5
      "# Tracker dashboards (systemd tracker-kpi :3313, tracker-ladder :3340)\n"
        ++ "# Security: gated — session cookie or ops edge basic-auth.\n\n"
      ""
      ""
      ""
      ""
    -- Tracker Fleet
    Spec.mk "tracker-fleet" "Watch Fleet Supervisor (:3329)" .node
      "/home/mdupont/projects/twitterstorm/tracker" "node src/fleet.mjs" ""
      3329 "/tracker/fleet/" false false false 60 "always" 5
      "# Watch Fleet Supervisor (:3329) — multi-agent watch KPIs\n\n"
      ""
      ""
      ""
      ""
    -- Tracker Image Proxy
    Spec.mk "tracker-image-proxy" "Tracker full image (chroot :8098)" .node
      "/home/mdupont/projects/twitterstorm/tracker-image" "node proxy.mjs" ""
      8098 "/tracker/image/" false true false 60 "always" 5
      "# Tracker full image (chroot) — tracker-image@full.service\n"
        ++ "# In-image nginx (127.0.0.1:8098) fronts the in-image dashboards:\n"
        ++ "#   /kpi/     → unified server      (PORT,          default 3313)\n"
        ++ "#   /archive/ → archive server      (ARCHIVE_PORT,  default 3314)\n"
        ++ "#   /ladder/  → ladder console      (DASHBOARD_PORT,default 3340)\n\n"
      ""
      ""
      ""
      ""
    -- Tracker Panel
    Spec.mk "tracker-panel" "Tracker control-plane panel (:3321)" .node
      "/home/mdupont/projects/twitterstorm/tracker" "node src/panel.mjs" ""
      3321 "/tracker/panel/" true true false 120 "always" 5
      "# Tracker control-plane panel (systemd tracker-panel.service, 127.0.0.1:3321)\n"
        ++ "# Security: panel API requires vault bearer token on every route.\n\n"
      ""
      ""
      ""
      ""
    -- Twitterstorm Report (static)
    Spec.mk "twitterstorm-report" "Twitterstorm status & test report (static)" .static
      "/home/mdupont/projects/twitterstorm/report" "" ""
      0 "/twitterstorm/report/" false true false 120 "always" 5
      "# Twitterstorm status & test report (static, generated by scripts/build-status-report.mjs)\n"
        ++ "# Served at /twitterstorm/report/ — longer prefix than /twitterstorm/ panel.\n\n"
      ""
      ""
      ""
      ""
    -- Twitter Tracker
    Spec.mk "twitter-tracker" "Twitter Tracker Unified Server (:3313)" .node
      "/home/mdupont/projects/twitterstorm/tracker" "node src/tracker.mjs" ""
      3313 "/twitterstorm/" true true false 120 "always" 5
      "# Twitter Tracker Unified Server (Port 3313)\n"
        ++ "# Edge gate: session cookie OR legacy ops basic-auth pair.\n\n"
      ""
      ""
      ""
      ""
  ]

/-- Main entry point: `lean --run ServiceSpec.lean [publish DIR]` -/
def main (argv : List String) : IO UInt32 := do
  match argv with
  | [] => IO.println ServiceSpec.renderAll; pure 0
  | ["publish", dir] => ServiceSpec.publish dir; pure 0
  | ["publish"] =>
    IO.eprintln "Usage: lean --run ServiceSpec.lean publish DIR"; pure 1
  | [s] =>
    match ServiceSpec.services.find? (fun x => x.name == s) with
    | some svc =>
      IO.println s!"# {svc.name}\n"
      IO.println "# ── nginx ─────────────────────────────────────────────\n"
      IO.println (ServiceSpec.emitNginx svc)
      IO.println "\n# ── systemd ─────────────────────────────────────────────\n"
      IO.println (ServiceSpec.emitSystemd svc)
      pure 0
    | none =>
      IO.eprintln s!"Unknown service: {s}"
      let names := (ServiceSpec.services.map (·.name)).join " "
      IO.eprintln s!"Available: {names}"
      pure 1
  | _ =>
    IO.eprintln "Usage: lean --run ServiceSpec.lean [publish DIR] [service-name]"
    pure 1
