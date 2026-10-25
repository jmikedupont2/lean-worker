# Plugin Negotiation — Task Spec

## Role
Task-runner plugin layer for Gokujo: tasks declare tools/skills/allowlist
entries/permissions up-front; negotiation resolves them before the agent
runs, so nothing is discovered blocked mid-execution.

## Domain

### Purpose
Fix the failure mode seen on 2026-10-24 in `/mnt/data1/tmux`: the recovery
task needed six llm-agents binaries (`agentsview`, `ccusage`,
`cpa-usage-keeper`, `entire`, `mindwalk`, `tokscale`), none of which were in
the lean-ctx shell allowlist. Each invocation returned a *permanent*
`[BLOCKED]`, and the run stalled waiting for user remediation.

### Problem
- Prerequisites (tools, skills, allowlist entries, ports, dirs) were resolved
  lazily — at first use — instead of during task negotiation.
- lean-ctx blocks are permanent per command; a blocked binary forces a
  config write (`lean-ctx allow <cmd>` or `shell_security = "off"`).
- No formal notion of "what the agent needs" existed in the gokujo registry.

### Key Issues
- `Agents/Protocols/*.lean` were byte-corrupted (NUL where `∀` belongs,
  0x17 where `×` belongs) → repaired 2026-10-25, files now valid UTF-8.
- `| Custom of String` bare-`of` constructor syntax does not parse in Lean
  4.30; must be `(of : String)` → fixed in Registry.lean; still present in
  AgentProtocols.lean / MCP.lean / ToolCalling.lean.

## Proposed Changes
1. `Plugins/PluginNegotiation.lean` — Prerequisite / Host / NegotiationRequest
   / NegotiationOutcome / Plugin / PluginRegistry + decide-able negotiation.
2. `Plugins/LeanCtx.lean` — lean-ctx as a plugin (allowlist gating,
   config.toml, tee archive dir) and the concrete `llmAgentsToolsRequest`.
3. `Plugins/AgentTelemetry.lean` — the six llm-agents tools as declarative
   plugins with per-tool prerequisites (sources probed, not assumed).
4. `Agents/Protocols/Registry.lean` — `ProtocolName.LeanCtx` +
   `.AgentTelemetry` constructors and `defaultProtocolRegistry` entries.

## Files to Modify
```
tools/gokujo/Plugins/PluginNegotiation.lean   (new, standalone, compiles)
tools/gokujo/Plugins/LeanCtx.lean             (new, compiles, 1 documented sorry)
tools/gokujo/Plugins/AgentTelemetry.lean      (new, compiles clean)
tools/gokujo/Agents/Protocols/Registry.lean   (wired; parse-checked standalone)
```

## Entry
```bash
cd ~/projects/lean-worker/tools/gokujo
mkdir -p /tmp/plugincheck/Plugins
lean Plugins/PluginNegotiation.lean -o /tmp/plugincheck/Plugins/PluginNegotiation.olean
LEAN_PATH=/tmp/plugincheck lean Plugins/LeanCtx.lean
LEAN_PATH=/tmp/plugincheck lean Plugins/AgentTelemetry.lean
```

## Acceptance Criteria
- [x] All three Plugins files type-check standalone (Lean 4.30).
- [x] Negotiation model covers: executables, allowlist entries, config
      files/dirs, data/writable dirs, network, ports, services, secrets.
- [x] The 2026-10-24 blocked run is expressed as a `NegotiationRequest`.
- [x] Registry.lean carries the two new protocol entries;
      `createAdapterForProtocol` fallback `| _ => none` absorbs them.
- [ ] Full-tree `lake build` once `gokujo-protocol-registry-overhaul` lands
      (bare-`of` syntax debt in the sibling protocol files).
- [ ] `negotiate_granted_implies_supported` sorry removed (needs
      `List.filter_eq_nil_iff` bridge).
