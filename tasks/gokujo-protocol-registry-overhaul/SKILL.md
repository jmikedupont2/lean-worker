---
name: gokujo-protocol-registry-overhaul
description: Overhaul the Gokujo Agent Protocol Library — deduplicate types, implement ProtocolDiscoveryService, wire up real defaults
---

# gokujo-protocol-registry-overhaul

## Goal

Make the Agent Protocol Library actually useful by turning the type definitions into a working registry with real defaults and no redundant code.

## Entry

Read `SYSTEM.md` for full context, then:

```bash
cd /mnt/data1/time-2026/09-september/18/lean-worker
# Review all protocol files
grep -n "sorry" tools/gokujo/Agents/Protocols/*.lean
# Check what imports what
head -10 tools/gokujo/Agents/Protocols/AgentProtocols.lean
head -10 tools/gokujo/Agents/Protocols/Registry.lean
# Verify build currently works
lake build 2>&1 | tail -5
```

## Key Files

```
tools/gokujo/Agents/Protocols/
├── AgentProtocols.lean    # 10 category enums + allAgentProtocols (100+) — DEDUPLICATE
├── MCP.lean                # MCP types — KEEP AS-IS (real types)
├── ToolCalling.lean        # Function calling types — KEEP AS-IS (real types)
└── Registry.lean           # Protocol registry — ADD searchProtocols, real defaults
```

## Approach

1. First, read all 4 files completely
2. Move `allAgentProtocols` and `ProtocolCategory` into `Registry.lean`
3. Rewrite `AgentProtocols.lean` to only contain:
   - The 10-category enum (keep)
   - The `allAgentProtocols` list (moved here)
   - Theorems proving coverage
4. Implement `ProtocolDiscoveryService.searchProtocols` in `Registry.lean`
5. Populate `defaultProtocolRegistry` with real entries (non-empty configs)
6. Add `sorry`-free theorems
7. Run `lake build` to verify
