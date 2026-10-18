---
name: gokujo-mcp-stdio-execution
description: Wire up real MCP stdio execution in Gokujo — JSON-RPC client, stdio subprocess, built-in servers
---

# gokujo-mcp-stdio-execution

## Goal

Replace all `sorry` in MCP execution functions with real stdio-based JSON-RPC communication with MCP servers.

## Entry

Read `SYSTEM.md` for full context, then:

```bash
cd /mnt/data1/time-2026/09-september/18/lean-worker
# Verify MCP inspector works
echo '{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"protocolVersion":"2024-11-05","capabilities":{},"clientInfo":{"name":"test","version":"0.1"}}}' | npx @modelcontextprotocol/inspector --transport stdio 2>&1 | head -3
# Check current sorry count
grep -c "sorry" tools/gokujo/Agents/Protocols/MCP.lean
```

## Key File

```
tools/gokujo/Agents/Protocols/MCP.lean
```

This is the only file that needs changes. `AgentProtocols.lean` and `ToolCalling.lean` are fine as-is.

## Approach

1. Read `MCP.lean` completely (it's ~500 lines of types + sorry stubs)
2. Add JSON-RPC 2.0 types at the top
3. Implement `StdioMCPClient` with spawn/read/write/close
4. Implement `connectMCPClient` using the stdio client
5. Implement `startMCPServer` spawning `npx @modelcontextprotocol/inspector`
6. Implement `executeMCPToolCall` sending `tools/call` request
7. Implement `executeMCPResourceRead` sending `resources/read` request
8. Add helper `withMCPServer` for context-managed server lifecycle
9. Run `lake build`

## Architecture

```
Lean (StdioMCPClient)
  ├── spawn: npx @modelcontextprotocol/inspector --transport stdio
  ├── write: JSON-RPC 2.0 request (tools/call or resources/read)
  ├── read:  JSON-RPC 2.0 response from server stdout
  └── return: MCPExecutionResult
```
