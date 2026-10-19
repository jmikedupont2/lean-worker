# Task: gokujo-mcp-stdio-execution

- **Priority:** P0
- **Name:** gokujo-mcp-stdio-execution
- **Area:** gokujo, mcp, agent-protocols
- **Depends on:** []
- **Status:** open

# Role

Contributor (Lean 4)

# Domain

gokujo, mcp, stdio, protocol-execution

## Purpose

Wire up real MCP (Model Context Protocol) stdio/stdout execution so that Gokujo can actually communicate with MCP servers like the filesystem server, GitHub server, etc. Currently all `executeMCPToolCall` and `executeMCPResourceRead` functions are `sorry`.

## Workdir

`/mnt/data1/time-2026/09-september/18/lean-worker`

## State

- Open claims: 0
- Services tracked: 0

## Problem

The MCP module in `tools/gokujo/Agents/Protocols/MCP.lean` defines complete types for MCP servers, clients, tools, resources, prompts, and messages — but every execution function is `sorry`:

```lean
def executeMCPToolCall
  (context : MCPExecutionContext)
  (tool_call : ToolCall)
  : IO MCPExecutionResult := by
  sorry

def executeMCPResourceRead
  (context : MCPExecutionContext)
  (resource : Resource)
  : IO MCPExecutionResult := by
  sorry

def startMCPServer
  (server : Server)
  : IO Server := by
  sorry

def connectMCPClient
  (client : Client)
  (server_config : ServerConfig)
  : IO Client := by
  sorry
```

The built-in MCP servers (filesystem, github, git) are defined with real tool definitions and resource templates, but there's no way to actually execute them.

### Architecture

```
MCP Client (Lean)              MCP Server (external, e.g. npx @modelcontextprotocol/inspector)
       |                                  |
       |-- stdio std::out -->           |
       | <-- std::in --|                |
       |                                  |
       |-- JSON-RPC 2.0 -->             |
       | <-- JSON-RPC 2.0 --|            |
```

The Lean MCP client needs to:
1. Spawn the MCP server as a subprocess
2. Send `initialize` JSON-RPC request
3. Handle `tools/list`, `tools/call`, `resources/read`, `prompts/get` requests
4. Parse responses and return `MCPExecutionResult`

## Proposed Changes

### 1. Add JSON-RPC types

```lean
structure JsonRpcRequest where
  jsonrpc : String
  id : Nat
  method : String
  params : String  -- JSON

structure JsonRpcResponse where
  jsonrpc : String
  id : Nat
  result : Option String  -- JSON
  error : Option JsonRpcError

structure JsonRpcError where
  code : Int
  message : String
  data : Option String
```

### 2. Implement stdio MCP client

```lean
structure StdioMCPClient where
  process : Process
  buffer : String

def connectStdioClient
  (serverPath : String)
  (args : List String)
  (env : List (String × String))
  : IO StdioMCPClient

def sendRequest
  (client : StdioMCPClient)
  (request : JsonRpcRequest)
  : IO JsonRpcResponse

def callTool
  (client : StdioMCPClient)
  (toolName : String)
  (arguments : String)
  : IO ToolCallResult

def readResource
  (client : StdioMCPClient)
  (uri : String)
  : IO ResourceReadResult
```

### 3. Wire up built-in servers

```lean
def startFilesystemMCPServer : IO Server :=
  connectStdioServer "npx" ["@modelcontextprotocol/inspector", "--transport", "stdio"]

def startGitHubMCPServer (token : String) : IO Server :=
  connectStdioServer "npx" ["@modelcontextprotocol/server-github", "--token", token]

def startGitMCPServer : IO Server :=
  connectStdioServer "npx" ["@modelcontextprotocol/server-git"]
```

### 4. Implement executeMCPToolCall

```lean
def executeMCPToolCall
  (context : MCPExecutionContext)
  (tool_call : ToolCall)
  : IO MCPExecutionResult := do
  let client ← connectStdioClient "npx" ["@modelcontextprotocol/inspector", "--transport", "stdio"] []
  let result ← callTool client tool_call.name tool_call.arguments
  return { success := true, content := result.content, tool_calls := [], error := none }
```

### 5. Add execution context helpers

```lean
def withMCPServer
  (serverConfig : ServerConfig)
  (f : StdioMCPClient → IO α)
  : IO α := do
  match serverConfig.name with
  | "filesystem" => do
      let client ← startFilesystemMCPServer
      f client
  | "github" => do
      -- extract token from config
      f client
  | _ => throw $ IO.userError s!"Unknown MCP server: {serverConfig.name}"
```

## Files to Modify

| File | Action |
|------|--------|
| `tools/gokujo/Agents/Protocols/MCP.lean` | Add JSON-RPC types, StdioMCPClient, implement `executeMCPToolCall`, `executeMCPResourceRead`, `startMCPServer`, `connectMCPClient` |
| `tools/gokujo/Agents/Protocols/ToolCalling.lean` | No changes needed |
| `tools/gokujo/Agents/Protocols/AgentProtocols.lean` | No changes needed |

## Entry

```bash
cd /mnt/data1/time-2026/09-september/18/lean-worker
# Check current sorry count
grep -n "sorry" tools/gokujo/Agents/Protocols/MCP.lean
# Test that npx MCP inspector works
echo '{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"protocolVersion":"2024-11-05","capabilities":{},"clientInfo":{"name":"test","version":"0.1"}}}' | npx @modelcontextprotocol/inspector --transport stdio 2>&1 | head -5
```

## Acceptance Criteria

- [ ] `executeMCPToolCall` is sorry-free
- [ ] `executeMCPResourceRead` is sorry-free
- [ ] `startMCPServer` is sorry-free
- [ ] `connectMCPClient` is sorry-free
- [ ] Built-in servers (filesystem, github, git) have real implementations
- [ ] `lake build` succeeds after changes
- [ ] Manual test: `lake exe lean-worker --mcp filesystem --tool "list_directory" --args '{"path":"."}'` returns directory listing
