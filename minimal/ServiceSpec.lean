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

def services : List Spec :=
  let a : List Spec := [
    {
      name := "agentaps";
      description := "Agentaps desktop workspace";
      kind := .node;
      workingDir := "/home/mdupont/projects/agentaps";
      exec := "node server.mjs";
      port := 3000;
      path := "/agentaps/";
      proxyTimeout := 60;
    }
    {
      name := "aristo";
      description := "Aristotle WASM UI + API";
      kind := .static;
      workingDir := "/mnt/data1/time-2026/05-may/07/arist/www";
      port := 9876;
      path := "/aristo/";
      auth := false;
      cors := true;
      nginxHeader := "# Consolidated Aristotle nginx configuration\n# Included from solana.solfunmeme.com TLS vhost via services.d/*.conf\n#\n#   /aristo                          → static WASM UI (www/)\n#   /aristo/api/                     → aristotle-manager serve :9876\n#   /aristo/health                   → aristotle-manager health\n#   /aristo/verify                   → aristotle-manager verify endpoint\n#   /aristo/plan                     → DASP planner tile (:8888)\n#   /aristo/alias-web                → alias-web :8083\n#\n# Disabled: /aristo/gokujo/*, /aristo/gui2proof/*, /aristo/p2p/*, /aristo/file-drop/*\n#";
      nginxExtra := "# Static WASM UI: serves www/ with SPA fallback\n"
        ++ "location ^~ /aristo/ {\n"
        ++ "    alias /mnt/data1/time-2026/05-may/07/arist/www/;\n"
        ++ "    index index.html;\n"
        ++ "    try_files $uri $uri/ /aristo/index.html;\n"
        ++ "    add_header Cache-Control \"public, max-age=300\";\n"
        ++ "    types { application/wasm wasm; }\n"
        ++ "}\n";
    }
  ]
  let b : List Spec := [
    {
      name := "cloudflare-coordination";
      description := "Cloudflare Coordination Dashboard";
      kind := .static;
      workingDir := "/home/mdupont/projects/twitterstorm/cloudflare";
      port := 0;
      path := "/cloudflare/";
      auth := false;
      cors := true;
      nginxHeader := "# Cloudflare Coordination Dashboard — /cloudflare/\n"
        ++ "# Static site from twitterstorm/cloudflare/\n"
        ++ "access_log /var/log/nginx/cloudflare-dashboard.log combined;\n\n";
    }
    {
      name := "concept-api";
      description := "Concept/Value lattice API";
      kind := .python;
      workingDir := "/home/mdupont/2026/concept-lattice-web";
      exec := "concept_api.py";
      port := 9999;
      path := "/concept/";
      proxyTimeout := 120;
    }
    {
      name := "control-node";
      description := "Control Node (TypeScript Worker :8808)";
      kind := .node;
      workingDir := "/home/mdupont/projects/twitterstorm/control-node";
      exec := "src/index.ts";
      port := 8808;
      path := "/control-node/";
      auth := false;
      proxyTimeout := 60;
      nginxHeader := "# Control Node (Port 8808 - TypeScript Worker)\n";
    }
    {
      name := "forgejo";
      description := "Forgejo git forge";
      kind := .node;
      workingDir := "/home/mdupont/projects/forgejo";
      exec := "node server.js";
      port := 3000;
      path := "/forgejo/";
      auth := false;
      cors := true;
      nginxHeader := "# Forgejo git forge — Gitea/Forgejo subpath deployment\n"
        ++ "# Auth: Forgejo's own user/token auth governs.\n\n";
    }
    {
      name := "golive-deck";
      description := "Go-live control deck";
      kind := .node;
      workingDir := "/home/mdupont/projects/twitterstorm/golive-deck";
      exec := "node deck.mjs";
      port := 3341;
      path := "/golive/";
      auth := false;
      cors := true;
      proxyTimeout := 120;
      nginxHeader := "# Go-live control deck (loopback :3341). Auth is app-level.\n"
        ++ "# /health stays public for uptime probes.\n\n";
    }
    {
      name := "golive-branch-base";
      description := "Go-live branch preview base";
      kind := .node;
      workingDir := "/home/mdupont/projects/twitterstorm/golive-branch-base";
      exec := "server.mjs";
      port := 38888;
      path := "/golive/branch/";
      auth := false;
      proxyTimeout := 60;
      nginxHeader := "# Go-Live Base branch — fronts the go-live server on port 38888\n"
        ++ "# URL: https://solana.solfunmeme.com/twitterstorm/golive/branchname/\n"
        ++ "# Backend: http://127.0.0.1:38888\n"
        ++ "# Internal test API only (no external dependencies)\n\n";
    }
  ]
  let c : List Spec := [
    {
      name := "gui2proof";
      description := "DASL GUI2Proof service (Lean's GUI-proof side)";
      kind := .node;
      workingDir := "/mnt/data1/time-2026/05-may/07/arist";
      exec := "scripts/start-gui2proof.mjs";
      port := 9890;
      path := "/gui2proof/";
      auth := true;
      cors := true;
      proxyTimeout := 180;
      websocket := false;
      nginxHeader := "# GUI2Proof control surface; the service binds only to localhost.\n"
        ++ "# EDGE-GATED: unauthenticated trigger through the vhost.\n"
        ++ "# Gated with the tracker auth_request machinery.\n\n";
    }
    {
      name := "kant-relay";
      description := "Kant ZK Rendezvous Relay";
      kind := .node;
      workingDir := "/home/mdupont/projects/kant-zk-pastebin";
      exec := "server/relay.mjs";
      args := "--port 8787 --host 127.0.0.1";
      port := 8787;
      path := "/relay/";
      auth := false;
      websocket := true;
      proxyTimeout := 86400;
      cors := true;
      nginxHeader := "# kant-zk relay — node twin at 127.0.0.1:8787\n"
        ++ "# PUBLIC: rooms are unguessable; access is via shared links.\n\n";
    }
    {
      name := "pastebin";
      description := "Kant Pastebin";
      kind := .node;
      workingDir := "/home/mdupont/projects/kant-pastebin";
      exec := "node server.mjs";
      port := 8090;
      path := "/pastebin/";
      auth := false;
      cors := true;
      proxyTimeout := 120;
      nginxHeader := "# Kant Pastebin (Port 8090)\n";
    }
    {
      name := "sparql-gui";
      description := "SPARQL GUI";
      kind := .python;
      workingDir := "/home/mdupont/projects/sparql-gui";
      exec := "app.py";
      port := 8088;
      path := "/sparql-gui/";
      auth := false;
      cors := true;
      proxyTimeout := 120;
    }
    {
      name := "tracker-agents";
      description := "Tracker agent control (tmux/agents :3313)";
      kind := .node;
      workingDir := "/home/mdupont/projects/twitterstorm/tracker";
      exec := "node src/agents.mjs";
      port := 3313;
      path := "/tracker/agents/";
      auth := true;
      proxyTimeout := 60;
      nginxHeader := "# Tracker agent control (tmux/agents surface of :3313)\n"
        ++ "# Edge gate: session cookie OR legacy ops basic-auth pair.\n\n";
    }
    {
      name := "tracker-dashboards";
      description := "Tracker dashboards (KPI :3313, ladder :3340)";
      kind := .node;
      workingDir := "/home/mdupont/projects/twitterstorm/tracker";
      exec := "node src/dashboards.mjs";
      port := 3313;
      path := "/tracker/";
      auth := true;
      cors := true;
      proxyTimeout := 120;
      nginxHeader := "# Tracker dashboards (systemd tracker-kpi :3313, tracker-ladder :3340)\n"
        ++ "# Security: gated — session cookie or ops edge basic-auth.\n\n";
    }
  ]
  let d : List Spec := [
    {
      name := "tracker-fleet";
      description := "Watch Fleet Supervisor (:3329)";
      kind := .node;
      workingDir := "/home/mdupont/projects/twitterstorm/tracker";
      exec := "node src/fleet.mjs";
      port := 3329;
      path := "/tracker/fleet/";
      auth := false;
      proxyTimeout := 60;
      nginxHeader := "# Watch Fleet Supervisor (:3329) — multi-agent watch KPIs\n\n";
    }
    {
      name := "tracker-image-proxy";
      description := "Tracker full image (chroot :8098)";
      kind := .node;
      workingDir := "/home/mdupont/projects/twitterstorm/tracker-image";
      exec := "node proxy.mjs";
      port := 8098;
      path := "/tracker/image/";
      auth := false;
      cors := true;
      proxyTimeout := 60;
      nginxHeader := "# Tracker full image (chroot) — tracker-image@full.service\n"
        ++ "# In-image nginx (127.0.0.1:8098) fronts the in-image dashboards:\n"
        ++ "#   /kpi/     → unified server      (PORT,          default 3313)\n"
        ++ "#   /archive/ → archive server      (ARCHIVE_PORT,  default 3314)\n"
        ++ "#   /ladder/  → ladder console      (DASHBOARD_PORT,default 3340)\n\n";
    }
    {
      name := "tracker-panel";
      description := "Tracker control-plane panel (:3321)";
      kind := .node;
      workingDir := "/home/mdupont/projects/twitterstorm/tracker";
      exec := "node src/panel.mjs";
      port := 3321;
      path := "/tracker/panel/";
      auth := true;
      cors := true;
      proxyTimeout := 120;
      nginxHeader := "# Tracker control-plane panel (systemd tracker-panel.service, 127.0.0.1:3321)\n"
        ++ "# Security: panel API requires vault bearer token on every route.\n\n";
    }
    {
      name := "twitterstorm-report";
      description := "Twitterstorm status & test report (static)";
      kind := .static;
      workingDir := "/home/mdupont/projects/twitterstorm/report";
      port := 0;
      path := "/twitterstorm/report/";
      auth := false;
      cors := true;
      nginxHeader := "# Twitterstorm status & test report (static, generated by scripts/build-status-report.mjs)\n"
        ++ "# Served at /twitterstorm/report/ — longer prefix than /twitterstorm/ panel.\n\n";
    }
    {
      name := "twitter-tracker";
      description := "Twitter Tracker Unified Server (:3313)";
      kind := .node;
      workingDir := "/home/mdupont/projects/twitterstorm/tracker";
      exec := "node src/tracker.mjs";
      port := 3313;
      path := "/twitterstorm/";
      auth := true;
      cors := true;
      proxyTimeout := 120;
      nginxHeader := "# Twitter Tracker Unified Server (Port 3313)\n"
        ++ "# Edge gate: session cookie OR legacy ops basic-auth pair.\n\n";
    }
  ] in a ++ b ++ c ++ d
      {
        name := "agentaps";
        description := "Agentaps desktop workspace";
        kind := .node;
        workingDir := "/home/mdupont/projects/agentaps";
        exec := "node server.mjs";
        port := 3000;
        path := "/agentaps/";
        proxyTimeout := 60;
      }
      {
        name := "aristo";
        description := "Aristotle WASM UI + API";
        kind := .static;
        workingDir := "/mnt/data1/time-2026/05-may/07/arist/www";
        port := 9876;
        path := "/aristo/";
        auth := false;
        cors := true;
        nginxHeader := "# Consolidated Aristotle nginx configuration\n# Included from solana.solfunmeme.com TLS vhost via services.d/*.conf\n#\n#   /aristo                          → static WASM UI (www/)\n#   /aristo/api/                     → aristotle-manager serve :9876\n#   /aristo/health                   → aristotle-manager health\n#   /aristo/verify                   → aristotle-manager verify endpoint\n#   /aristo/plan                     → DASP planner tile (:8888)\n#   /aristo/alias-web                → alias-web :8083\n#\n# Disabled: /aristo/gokujo/*, /aristo/gui2proof/*, /aristo/p2p/*, /aristo/file-drop/*\n#";
        nginxExtra := "# Static WASM UI: serves www/ with SPA fallback\n"
          ++ "location ^~ /aristo/ {\n"
          ++ "    alias /mnt/data1/time-2026/05-may/07/arist/www/;\n"
          ++ "    index index.html;\n"
          ++ "    try_files $uri $uri/ /aristo/index.html;\n"
          ++ "    add_header Cache-Control \"public, max-age=300\";\n"
          ++ "    types { application/wasm wasm; }\n"
          ++ "}\n";
      }
      {
        name := "cloudflare-coordination";
        description := "Cloudflare Coordination Dashboard";
        kind := .static;
        workingDir := "/home/mdupont/projects/twitterstorm/cloudflare";
        port := 0;
        path := "/cloudflare/";
        auth := false;
        cors := true;
        nginxHeader := "# Cloudflare Coordination Dashboard — /cloudflare/\n"
          ++ "# Static site from twitterstorm/cloudflare/\n"
          ++ "access_log /var/log/nginx/cloudflare-dashboard.log combined;\n\n";
      }
      {
        name := "concept-api";
        description := "Concept/Value lattice API";
        kind := .python;
        workingDir := "/home/mdupont/2026/concept-lattice-web";
        exec := "concept_api.py";
        port := 9999;
        path := "/concept/";
        proxyTimeout := 120;
      }
      {
        name := "control-node";
        description := "Control Node (TypeScript Worker :8808)";
        kind := .node;
        workingDir := "/home/mdupont/projects/twitterstorm/control-node";
        exec := "src/index.ts";
        port := 8808;
        path := "/control-node/";
        auth := false;
        proxyTimeout := 60;
        nginxHeader := "# Control Node (Port 8808 - TypeScript Worker)\n";
      }
      {
        name := "forgejo";
        description := "Forgejo git forge";
        kind := .node;
        workingDir := "/home/mdupont/projects/forgejo";
        exec := "node server.js";
        port := 3000;
        path := "/forgejo/";
        auth := false;
        cors := true;
        nginxHeader := "# Forgejo git forge — Gitea/Forgejo subpath deployment\n"
          ++ "# Auth: Forgejo's own user/token auth governs.\n\n";
      }
      {
        name := "golive-deck";
        description := "Go-live control deck";
        kind := .node;
        workingDir := "/home/mdupont/projects/twitterstorm/golive-deck";
        exec := "node deck.mjs";
        port := 3341;
        path := "/golive/";
        auth := false;
        cors := true;
        proxyTimeout := 120;
        nginxHeader := "# Go-live control deck (loopback :3341). Auth is app-level.\n"
          ++ "# /health stays public for uptime probes.\n\n";
      }
      {
        name := "golive-branch-base";
        description := "Go-live branch preview base";
        kind := .node;
        workingDir := "/home/mdupont/projects/twitterstorm/golive-branch-base";
        exec := "server.mjs";
        port := 38888;
        path := "/golive/branch/";
        auth := false;
        proxyTimeout := 60;
        nginxHeader := "# Go-Live Base branch — fronts the go-live server on port 38888\n"
          ++ "# URL: https://solana.solfunmeme.com/twitterstorm/golive/branchname/\n"
          ++ "# Backend: http://127.0.0.1:38888\n"
          ++ "# Internal test API only (no external dependencies)\n\n";
      }
      {
        name := "gui2proof";
        description := "DASL GUI2Proof service (Lean's GUI-proof side)";
        kind := .node;
        workingDir := "/mnt/data1/time-2026/05-may/07/arist";
        exec := "scripts/start-gui2proof.mjs";
        port := 9890;
        path := "/gui2proof/";
        auth := true;
        cors := true;
        proxyTimeout := 180;
        websocket := false;
        nginxHeader := "# GUI2Proof control surface; the service binds only to localhost.\n"
          ++ "# EDGE-GATED: unauthenticated trigger through the vhost.\n"
          ++ "# Gated with the tracker auth_request machinery.\n\n";
      }
      {
        name := "kant-relay";
        description := "Kant ZK Rendezvous Relay";
        kind := .node;
        workingDir := "/home/mdupont/projects/kant-zk-pastebin";
        exec := "server/relay.mjs";
        args := "--port 8787 --host 127.0.0.1";
        port := 8787;
        path := "/relay/";
        auth := false;
        websocket := true;
        proxyTimeout := 86400;
        cors := true;
        nginxHeader := "# kant-zk relay — node twin at 127.0.0.1:8787\n"
          ++ "# PUBLIC: rooms are unguessable; access is via shared links.\n\n";
      }
      {
        name := "pastebin";
        description := "Kant Pastebin";
        kind := .node;
        workingDir := "/home/mdupont/projects/kant-pastebin";
        exec := "node server.mjs";
        port := 8090;
        path := "/pastebin/";
        auth := false;
        cors := true;
        proxyTimeout := 120;
        nginxHeader := "# Kant Pastebin (Port 8090)\n";
      }
      {
        name := "sparql-gui";
        description := "SPARQL GUI";
        kind := .python;
        workingDir := "/home/mdupont/projects/sparql-gui";
        exec := "app.py";
        port := 8088;
        path := "/sparql-gui/";
        auth := false;
        cors := true;
        proxyTimeout := 120;
      }
      {
        name := "tracker-agents";
        description := "Tracker agent control (tmux/agents :3313)";
        kind := .node;
        workingDir := "/home/mdupont/projects/twitterstorm/tracker";
        exec := "node src/agents.mjs";
        port := 3313;
        path := "/tracker/agents/";
        auth := true;
        proxyTimeout := 60;
        nginxHeader := "# Tracker agent control (tmux/agents surface of :3313)\n"
          ++ "# Edge gate: session cookie OR legacy ops basic-auth pair.\n\n";
      }
      {
        name := "tracker-dashboards";
        description := "Tracker dashboards (KPI :3313, ladder :3340)";
        kind := .node;
        workingDir := "/home/mdupont/projects/twitterstorm/tracker";
        exec := "node src/dashboards.mjs";
        port := 3313;
        path := "/tracker/";
        auth := true;
        cors := true;
        proxyTimeout := 120;
        nginxHeader := "# Tracker dashboards (systemd tracker-kpi :3313, tracker-ladder :3340)\n"
          ++ "# Security: gated — session cookie or ops edge basic-auth.\n\n";
      }
      {
        name := "tracker-fleet";
        description := "Watch Fleet Supervisor (:3329)";
        kind := .node;
        workingDir := "/home/mdupont/projects/twitterstorm/tracker";
        exec := "node src/fleet.mjs";
        port := 3329;
        path := "/tracker/fleet/";
        auth := false;
        proxyTimeout := 60;
        nginxHeader := "# Watch Fleet Supervisor (:3329) — multi-agent watch KPIs\n\n";
      }
      {
        name := "tracker-image-proxy";
        description := "Tracker full image (chroot :8098)";
        kind := .node;
        workingDir := "/home/mdupont/projects/twitterstorm/tracker-image";
        exec := "node proxy.mjs";
        port := 8098;
        path := "/tracker/image/";
        auth := false;
        cors := true;
        proxyTimeout := 60;
        nginxHeader := "# Tracker full image (chroot) — tracker-image@full.service\n"
          ++ "# In-image nginx (127.0.0.1:8098) fronts the in-image dashboards:\n"
          ++ "#   /kpi/     → unified server      (PORT,          default 3313)\n"
          ++ "#   /archive/ → archive server      (ARCHIVE_PORT,  default 3314)\n"
          ++ "#   /ladder/  → ladder console      (DASHBOARD_PORT,default 3340)\n\n";
      }
      {
        name := "tracker-panel";
        description := "Tracker control-plane panel (:3321)";
        kind := .node;
        workingDir := "/home/mdupont/projects/twitterstorm/tracker";
        exec := "node src/panel.mjs";
        port := 3321;
        path := "/tracker/panel/";
        auth := true;
        cors := true;
        proxyTimeout := 120;
        nginxHeader := "# Tracker control-plane panel (systemd tracker-panel.service, 127.0.0.1:3321)\n"
          ++ "# Security: panel API requires vault bearer token on every route.\n\n";
      }
      {
        name := "twitterstorm-report";
        description := "Twitterstorm status & test report (static)";
        kind := .static;
        workingDir := "/home/mdupont/projects/twitterstorm/report";
        port := 0;
        path := "/twitterstorm/report/";
        auth := false;
        cors := true;
        nginxHeader := "# Twitterstorm status & test report (static, generated by scripts/build-status-report.mjs)\n"
          ++ "# Served at /twitterstorm/report/ — longer prefix than /twitterstorm/ panel.\n\n";
      }
      {
        name := "twitter-tracker";
        description := "Twitter Tracker Unified Server (:3313)";
        kind := .node;
        workingDir := "/home/mdupont/projects/twitterstorm/tracker";
        exec := "node src/tracker.mjs";
        port := 3313;
        path := "/twitterstorm/";
        auth := true;
        cors := true;
        proxyTimeout := 120;
        nginxHeader := "# Twitter Tracker Unified Server (Port 3313)\n"
          ++ "# Edge gate: session cookie OR legacy ops basic-auth pair.\n\n";
      }
    ]
  in svcs

/-! ## 3. Rendering -/

/-- The shell command used to start the service. Empty for static services. -/
def kindCmd (k : Kind) : String :=
  match k with
  | .node   => "node"
  | .rust   => ""
  | .python => "python3"
  | .lean   => "lean"
  | .static => ""

/-- ExecStart string: kind + exec + args, trimmed. Empty for static. -/
def kindExec (s : Spec) : String :=
  if s.exec.isEmpty then ""
  else
    let k := kindCmd s.kind
    if k.isEmpty then s.exec
    else k ++ " " ++ s.exec

/-- Common proxy headers for all non-static services. -/
def proxyHeaders : String :=
  "    proxy_http_version 1.1;\n"
  ++ "    proxy_set_header Host $host;\n"
  ++ "    proxy_set_header X-Real-IP $remote_addr;\n"
  ++ "    proxy_set_header X-Forwarded-For $proxy_add_x_forwarded_for;\n"
  ++ "    proxy_set_header X-Forwarded-Proto $scheme;\n"

/-- Generate nginx config for one service. -/
def emitNginx (s : Spec) : String :=
  let path := s.path
  -- redirect for non-root paths
  let redirect := if path.length > 1 then
    "location = " ++ path.dropEnd 1 ++ " {\n"
    ++ "    return 301 " ++ path ++ ";\n"
    ++ "}\n\n"
  else ""
  -- the main location block
  let location := "location ^~ " ++ path ++ " {\n"
  -- auth
  let authBlock := if s.auth then
    "    auth_request /_authcheck;\n"
    ++ "    error_page 401 = @tracker_login;\n"
  else ""
  -- proxy vs alias
  let proxyOrAlias :=
    if s.kind == .static then
      "    alias " ++ s.workingDir ++ "/;\n"
    else
      let exec := kindExec s
      let p := "    proxy_pass http://127.0.0.1:" ++ toString s.port ++ "/;\n"
      p ++ proxyHeaders
  -- websocket
  let wsBlock := if s.websocket then
    "    proxy_set_header Upgrade $http_upgrade;\n"
    ++ "    proxy_set_header Connection \"upgrade\";\n"
  else ""
  -- timeout
  let timeoutBlock := if s.proxyTimeout > 0 then
    "    proxy_read_timeout " ++ toString s.proxyTimeout ++ "s;\n"
  else ""
  -- buffering (Node.js services)
  let bufBlock := if s.kind == .node then
    "    proxy_buffering off;\n"
  else ""
  -- CORS
  let corsBlock := if s.cors then
    "    add_header Access-Control-Allow-Origin \"*\" always;\n"
  else ""
  -- extra
  let extra := s.nginxExtra
  s.nginxHeader ++ redirect ++ location
    ++ authBlock ++ proxyOrAlias ++ wsBlock ++ timeoutBlock ++ bufBlock ++ corsBlock
    ++ extra ++ "}\n"

/-- Generate systemd unit for one service. -/
def emitSystemd (s : Spec) : String :=
  if s.kind == .static then
    "-- Static service (no ExecStart — nginx alias + try_files handles it)\n"
  else
    let envBlock := if s.env.isEmpty then ""
      else "    environment = {\n"
        ++ String.intercalate "\n" ((s.env.splitOn "\n").filter (· != "")).map (fun l => "      " ++ l)
        ++ "\n    };\n"
    let scExtra := s.serviceConfigExtra
    "{\n"
    ++ "  description = \"" ++ s.description ++ "\";\n"
    ++ "  after = [ \"network.target\" ];\n"
    ++ "  wantedBy = [ \"system-manager.target\" ];\n"
    ++ "  serviceConfig = {\n"
    ++ "    Type = \"simple\";\n"
    ++ "    User = \"mdupont\";\n"
    ++ "    Group = \"mdupont\";\n"
    ++ "    WorkingDirectory = \"" ++ s.workingDir ++ "\";\n"
    ++ "    Restart = \"" ++ s.restart ++ "\";\n"
    ++ "    RestartSec = " ++ toString s.restartSec ++ ";\n"
    ++ "    StandardOutput = \"journal\";\n"
    ++ "    StandardError = \"journal\";\n"
    ++ scExtra
    ++ "  };\n"
    ++ envBlock
    ++ s.systemdExtra
    ++ "}\n"

/-- Render all configs and print. -/
def renderAll : String :=
  let nginx := List.map (fun s =>
    "# ── nginx: " ++ s.name ++ ".conf ───────────────────────\n" ++ emitNginx s) services
  let systemd := List.map (fun s =>
    "# ── systemd: " ++ s.name ++ ".nix ──────────────────────\n" ++ emitSystemd s) services
  "# ServiceSpec — generated nginx + systemd configs\n"
  ++ "# Edit this file, then:  lean --run ServiceSpec.lean\n"
  ++ "# To publish: lean --run ServiceSpec.lean publish DIR\n\n"
  ++ "# NGINX CONFIGS\n"
  ++ "# ═══════════════════════════════════════════════════════════════════════════\n\n"
  ++ String.intercalate "\n\n" nginx
  ++ "\n\n# SYSTEMD UNITS\n# ═══════════════════════════════════════════════════════════════════════════\n\n"
  ++ String.intercalate "\n\n" systemd

/-! ## 4. Publishing -/

/-- Publish generated configs into a system-manager checkout.
    Usage: lean --run ServiceSpec.lean publish /path/to/system-manager -/
def publish (systemManagerDir : String) : IO Unit := do
  let outDir := systemManagerDir ++ "/generated"
  IO.println s!"Publishing {services.length} service(s) to {outDir}/"
  for s in services do
    let nginx := emitNginx s
    let systemd := emitSystemd s
    let nginxPath := s!"{outDir}/nginx-{s.name}.conf"
    let systemdPath := s!"{outDir}/systemd-{s.name}.nix"
    IO.println s!"  {s.name}: nginx → {nginxPath}"
    IO.println s!"  {s.name}: systemd → {systemdPath}"
    IO.FS.writeFile nginxPath nginx
    IO.FS.writeFile systemdPath systemd
  IO.println "Done."

end ServiceSpec

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
