# Task: gokujo-protocol-registry-overhaul

- **Priority:** P1
- **Name:** gokujo-protocol-registry-overhaul
- **Area:** gokujo, tools, AgentProtocols
- **Depends on:** []
- **Status:** open

# Role

Contributor (Lean 4)

# Domain

gokujo, agent-protocols, type-system, registry

## Purpose

The `tools/gokujo/Agents/Protocols/` directory defines an Agent Protocol Library with 100+ protocol entries in `allAgentProtocols` but the type system is a stub framework — no real execution, no real adapter implementations, and `AgentProtocols.lean` redundantly re-exports everything from `MCP.lean`, `ToolCalling.lean`, and `Registry.lean`.

## Workdir

`/mnt/data1/time-2026/09-september/18/lean-worker`

## State

- Open claims: 0
- Services tracked: 0

## Problem

### Current State

```
tools/gokujo/Agents/Protocols/
├── AgentProtocols.lean    # 10 category enums + allAgentProtocols list (100+ entries)
├── MCP.lean                # MCP types + built-in servers (filesystem, github, git) — real types, sorry execution
├── ToolCalling.lean        # Function calling types + built-in tools — real types, sorry execution  
└── Registry.lean           # Protocol registry + default registry (~20 entries wired up)
```

The "1000+" in the module docstring is misleading — `allAgentProtocols` is ~100 metadata entries with `Custom of String` escape hatches. There are zero actual adapter implementations beyond type definitions.

### Key Issues

1. **`AgentProtocols.lean` re-exports everything** — imports `MCP`, `ToolCalling`, `Registry`, `Skills.Types`, `Skills.Adapter`, `Providers.Common`, then defines its own parallel type system (Category, ToolCallingProtocol, etc.) that shadows the real one from `MCP.lean` and `Registry.lean`. The `allAgentProtocols` list is a duplicate of what's already in `Registry.lean`.

2. **All execution functions are `sorry`** — `executeToolCall`, `executeMCPToolCall`, `bridgeToolCall`, `executeLeanSkillAdapter`, etc. are all `sorry`.

3. **No real provider integration** — OpenAI/Mistral/Anthropic adapters instantiate with empty tool lists `[]`.

4. **Registry is static** — `defaultProtocolRegistry` is a `def` computed once. No dynamic registration, no protocol selection by capability, no compatibility checking.

5. **Incomplete `ProtocolDiscoveryService`** — `searchProtocols` has an incomplete body referencing `entry.interface.protocol_name.toString` which won't compile (`.toString` on `ProtocolName` enum).

## Proposed Changes

### 1. Deduplicate type definitions

Remove the parallel type hierarchy in `AgentProtocols.lean`. Keep only:
- `ProtocolCategory` — the 10-category enum (moved to `Registry.lean` or a shared location)
- `allAgentProtocols` — the canonical list (move from `AgentProtocols.lean` to `Registry.lean`)

Delete the redundant enums (`ToolCallingProtocol`, `ReasoningProtocol`, `MultiAgentProtocol`, `MemoryProtocol`, `PlanningProtocol`, `ExecutionProtocol`, `CommunicationProtocol`, `LearningProtocol`, `EvaluationProtocol`) — these are already defined in `MCP.lean` and `Registry.lean`.

### 2. Remove stub types

Delete: `ReasoningAdapter`, `MultiAgentAdapter`, `MemoryAdapter`, `PlanningAdapter`, `ExecutionAdapter`, `CommunicationAdapter` — all defined as `def X := String`. These are not useful types.

### 3. Add ProtocolDiscoveryService implementation

```lean
structure ProtocolDiscoveryService where
  registry : ProtocolRegistry
  metadata : List ProtocolMetadata

def searchProtocols
  (service : ProtocolDiscoveryService)
  (capability : ProtocolCapability)
  (category : ProtocolCategory)
  : List ProtocolMetadata :=
  service.metadata.filter fun meta =>
    meta.category = category &&
    meta.capabilities.contains capability
```

### 4. Wire up real defaults

Populate the `defaultProtocolRegistry` with real adapter configs (not just `config := "{}"`). At minimum:
- MCP: filesystem + github servers
- OpenAI: function calling with built-in tools (calculator, code_interpreter, file_system)
- Anthropic: function calling

### 5. Add sorry-free theorems

Prove type invariants with `rfl`/`dec_trivial`/`decide`:
- Every protocol in `allAgentProtocols` has a matching entry in `defaultProtocolRegistry`
- `allAgentProtocols` covers all categories
- `defaultProtocolRegistry` contains no duplicates

## Files to Modify

| File | Action |
|------|--------|
| `tools/gokujo/Agents/Protocols/AgentProtocols.lean` | Major rewrite — deduplicate, remove stubs |
| `tools/gokujo/Agents/Protocols/Registry.lean` | Add `searchProtocols`, populate real defaults |
| `tools/gokujo/Agents/Protocols/MCP.lean` | No changes (real types) |
| `tools/gokujo/Agents/Protocols/ToolCalling.lean` | No changes (real types) |

## Entry

```bash
cd /mnt/data1/time-2026/09-september/18/lean-worker
# Review current state
grep -n "sorry" tools/gokujo/Agents/Protocols/*.lean
wc -l tools/gokujo/Agents/Protocols/*.lean
# Read the key files
cat tools/gokujo/Agents/Protocols/AgentProtocols.lean | head -120
cat tools/gokujo/Agents/Protocols/Registry.lean | tail -60
```

## Acceptance Criteria

- [ ] `AgentProtocols.lean` no longer imports `MCP`, `ToolCalling`, `Skills.Types`, `Skills.Adapter`, `Providers.Common`
- [ ] No `def X := String` stub types remain
- [ ] `allAgentProtocols` lives in `Registry.lean` (single source of truth)
- [ ] `ProtocolDiscoveryService.searchProtocols` compiles without sorry
- [ ] `defaultProtocolRegistry` has real entries (non-empty config, non-empty capabilities)
- [ ] All theorems in the file are sorry-free
- [ ] `lake build` succeeds after changes
