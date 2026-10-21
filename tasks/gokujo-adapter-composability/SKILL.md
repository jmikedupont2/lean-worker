---
name: gokujo-adapter-composability
description: Introduce ProtocolAdapter typeclass for composable adapters in Gokujo
---

# gokujo-adapter-composability

## Goal

Enable polymorphic adapter composition — write functions that work with any protocol adapter.

## Entry

Read `SYSTEM.md` for full context, then:

```bash
cd /mnt/data1/time-2026/09-september/18/lean-worker
# Review current adapter definitions
grep -n "structure.*Adapter" tools/gokujo/Agents/Protocols/MCP.lean tools/gokujo/Agents/Protocols/ToolCalling.lean tools/gokujo/Skills/Adapter.lean
# Check build
lake build 2>&1 | tail -3
```

## Key Files

```
tools/gokujo/Skills/Adapter.lean          # Add ProtocolAdapter typeclass here
tools/gokujo/Agents/Protocols/MCP.lean     # Add instance for MCPSkillAdapter
tools/gokujo/Agents/Protocols/ToolCalling.lean  # Add instance for ToolCallingAdapter
tools/gokujo/Agents/Protocols/AgentProtocols.lean   # Add instance for LeanSkillAdapter
```

## Approach

1. Read all 4 files completely
2. Add `ProtocolAdapter` typeclass to `Skills/Adapter.lean` with `execute`, `supports`, `protocolName`
3. Add `ProtocolAdapter` instance for `ToolCallingAdapter` in `ToolCalling.lean`
4. Add `ProtocolAdapter` instance for `MCPSkillAdapter` in `MCP.lean`
5. Add `ProtocolAdapter` instance for `LeanSkillAdapter` in `AgentProtocols.lean`
6. Add `findAdapter` to `Skills/Adapter.lean`
7. Add composition helper
8. Run `lake build`
