# Task: gokujo-adapter-composability

- **Priority:** P2
- **Name:** gokujo-adapter-composability
- **Area:** gokujo, adapter, composability
- **Depends on:** []
- **Status:** open

# Role

Contributor (Lean 4)

# Domain

gokujo, adapter, typeclass, composability

## Purpose

Currently every adapter in `tools/gokujo/` is a concrete structure (`ToolCallingAdapter`, `MCPSkillAdapter`, `LeanSkillAdapter`) with no shared interface. This makes it impossible to compose adapters or swap implementations. Introduce a `ProtocolAdapter` typeclass so adapters are polymorphic and composable.

## Workdir

`/mnt/data1/time-2026/09-september/18/lean-worker`

## State

- Open claims: 0
- Services tracked: 0

## Problem

### Current State

```lean
-- In ToolCalling.lean
structure ToolCallingAdapter where
  config : ToolCallingAdapterConfig
  skill_adapter : Skills.Adapter.LeanSkillAdapter
  function_mapping : List FunctionMapping

def ToolCallHandler := String  -- Lean function reference

-- In MCP.lean
structure MCPSkillAdapter where
  skill_adapter : Skills.Adapter.LeanSkillAdapter
  mcp_server : ServerConfig
  tool_mapping : List ToolMapping
  resource_mapping : List ResourceMapping

-- In Skills/Adapter.lean
structure LeanSkillAdapter where
  config : AdapterConfig
  skill_definition : SkillDefinition
  signature : LeanSkillSignature
  implementation : LeanSkillImplementation
  input_mapping : InputMapping
  output_mapping : OutputMapping
```

There is no common interface. To use a tool calling adapter, you need to know it's a `ToolCallingAdapter`. To use an MCP adapter, you need `MCPSkillAdapter`. There's no way to write a function that works with "any protocol adapter."

### What's Missing

1. **No shared protocol** — `ToolCallingAdapter`, `MCPSkillAdapter`, and `LeanSkillAdapter` are unrelated types
2. **No composition** — can't chain "MCP tool call" -> "Lean skill execution" -> "provider API call"
3. **No typeclass** — nothing enforces that adapters implement a common interface
4. **Adapter registry is untyped** — `AdapterRegistry := List LeanSkillAdapter` only holds one type

## Proposed Changes

### 1. Define ProtocolAdapter typeclass

```lean
class ProtocolAdapter (α : Type) where
  execute : α → ExecutionContext → IO ExecutionResult
  supports : α → ProtocolCapability → Bool
  protocolName : α → String
```

### 2. Add instances for existing adapters

```lean
instance : ProtocolAdapter ToolCallingAdapter where
  execute := ...
  supports cap := ...
  protocolName _ := "tool_calling"

instance : ProtocolAdapter MCPSkillAdapter where
  execute := ...
  supports cap := ...
  protocolName _ := "mcp"

instance : ProtocolAdapter LeanSkillAdapter where
  execute := ...
  supports cap := ...
  protocolName _ := "lean_skill"
```

### 3. Add composable pipeline builder

```lean
def compose [ProtocolAdapter A] [ProtocolAdapter B] :
  A → B → ExecutionContext → IO ExecutionResult := ...
```

### 4. Update AdapterRegistry to be heterogeneous

```lean
structure TypedAdapter where
  protocol : String
  adapter : ProtocolAdapter ?α  -- needs existential or separate handling

def AdapterRegistry := List TypedAdapter
```

### 5. Add adapter selection by capability

```lean
def findAdapter
  (registry : AdapterRegistry)
  (capability : ProtocolCapability)
  : List TypedAdapter :=
  registry.filter fun a => a.supports capability
```

## Files to Modify

| File | Action |
|------|--------|
| `tools/gokujo/Skills/Adapter.lean` | Add `ProtocolAdapter` typeclass, `findAdapter` function |
| `tools/gokujo/Agents/Protocols/ToolCalling.lean` | Add `ProtocolAdapter` instance for `ToolCallingAdapter` |
| `tools/gokujo/Agents/Protocols/MCP.lean` | Add `ProtocolAdapter` instance for `MCPSkillAdapter` |
| `tools/gokujo/Agents/Protocols/AgentProtocols.lean` | Add `ProtocolAdapter` instance for `LeanSkillAdapter` |

## Entry

```bash
cd /mnt/data1/time-2026/09-september/18/lean-worker
# Review current adapter definitions
cat tools/gokujo/Agents/Protocols/MCP.lean | grep "structure.*Adapter"
cat tools/gokujo/Agents/Protocols/ToolCalling.lean | grep "structure.*Adapter"
cat tools/gokujo/Skills/Adapter.lean | grep "structure.*Adapter"
```

## Acceptance Criteria

- [ ] `ProtocolAdapter` typeclass compiles
- [ ] `ToolCallingAdapter` has a `ProtocolAdapter` instance
- [ ] `MCPSkillAdapter` has a `ProtocolAdapter` instance
- [ ] `LeanSkillAdapter` has a `ProtocolAdapter` instance
- [ ] `findAdapter` function compiles
- [ ] `lake build` succeeds after changes
- [ ] Example composition: `compose mcpAdapter toolCallingAdapter context` type-checks
