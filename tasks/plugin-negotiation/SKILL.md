---
name: plugin-negotiation
description: Task-runner plugin layer — tasks declare tools/skills/allowlist/perms up-front; negotiation resolves them before the agent runs
---

# plugin-negotiation

## Goal

Make "what the agent needs" (tools, skills, lean-ctx allowlist entries,
config/data dirs, ports) part of task negotiation instead of a mid-run
surprise. Every plugin declares its prerequisites; `negotiate host req`
answers granted/blocked before any command is executed.

## Entry

Read `SYSTEM.md`, then verify the three plugin files type-check:

```bash
cd ~/projects/lean-worker/tools/gokujo
mkdir -p /tmp/plugincheck/Plugins
lean Plugins/PluginNegotiation.lean -o /tmp/plugincheck/Plugins/PluginNegotiation.olean
LEAN_PATH=/tmp/plugincheck lean Plugins/LeanCtx.lean
LEAN_PATH=/tmp/plugincheck lean Plugins/AgentTelemetry.lean
```

## Key Files

```
tools/gokujo/Plugins/
├── PluginNegotiation.lean   # Prerequisite/Host/NegotiationRequest/Outcome/Plugin
├── LeanCtx.lean             # lean-ctx plugin + llmAgentsToolsRequest
└── AgentTelemetry.lean      # agentsview, ccusage, cpa-usage-keeper,
                             # entire, mindwalk, tokscale as declared plugins
tools/gokujo/Agents/Protocols/Registry.lean   # .LeanCtx / .AgentTelemetry entries
```

## Usage in a task

Before running an agent command, the runner must:

1. Build a `Host` by probing the machine (`which`, config presence, services).
2. Collect `Plugin.prerequisites` for every plugin the task names.
3. `negotiate host req`; on `.blocked missing`, surface `blockRepairChoices`
   (e.g. `lean-ctx allow agentsview`) to the human **before** dispatch.

## Open Items

- Sorry bridge: `negotiate_granted_implies_supported`
  (`unmet = [] ⟹ prerequisites_supported`).
- Probe the six binaries (`--help`/`status`) and replace the placeholder
  data-source prerequisites with the exact dirs each tool reads.
- Convert sibling protocol files' bare `| Custom of String` to `(of : String)`.
