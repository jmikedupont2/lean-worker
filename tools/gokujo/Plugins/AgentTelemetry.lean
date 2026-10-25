-- AgentTelemetry.lean
-- The six llm-agents.nix observation tools as Gokujo task-runner plugins
--
-- Each plugin declares what it collects (capabilities), where it reads from
-- (data-directory prerequisites), and what the negotiation layer must grant
-- before a task may run it (allowlist entries, ports, dirs). Concrete
-- collection paths are verified by probing each binary at negotiation time
-- (`--help`/`status`), not assumed.

import Plugins.PluginNegotiation

namespace Plugins
namespace AgentTelemetry

open PrerequisiteKind

-- ============================================
-- Per-tool declarations
-- ============================================

-- agentsview (kenn-io) — local-first viewer + analytics for agent sessions
def agentsview : Plugin :=
  { id := .Custom "agentsview"
  , version := "0.45.0"
  , description := "Local-first viewer and analytics for AI coding agent sessions"
  , capabilities := [.SessionCapture, .SessionReplay, .Dashboard]
  , prerequisites :=
      [ { name := "agentsview", kind := .ExecutableOnPath
        , description := "Go binary; also ships an agentsview systemd unit" }
      , { name := "agent session roots", kind := .Custom "read set"
        , description := "~/.pi/agent/sessions, ~/.qoder/logs, ~/.local/share/{opencode,kilo,agent-deck}, ~/.letta — exact set probed at negotiation" }
      , { name := "agentsview serve port", kind := .ListeningPort
        , description := "web dashboard port when running `agentsview serve`" }
      ] }

-- ccusage (ccusage/rust) — token + cost analytics from local JSONL
def ccusage : Plugin :=
  { id := .Custom "ccusage"
  , version := "20.0.43"
  , description := "Analyze coding agent CLI token usage and costs from local data"
  , capabilities := [.TokenUsageAnalytics, .CostAccounting]
  , prerequisites :=
      [ { name := "ccusage", kind := .ExecutableOnPath
        , description := "Rust binary reading agent transcript JSONL" }
      , { name := "transcript JSONL roots", kind := .Custom "read set"
        , description := "session JSONL trees per agent (pi/qoder/kilo/opencode)" }
      ] }

-- cpa-usage-keeper (Willxup) — CliProxyAPI usage tracker
def cpaUsageKeeper : Plugin :=
  { id := .Custom "cpa-usage-keeper"
  , version := "2.0.0"
  , description := "Standalone CliProxyAPI usage tracker with SQLite persistence and dashboard"
  , capabilities := [.CostAccounting, .Dashboard]
  , prerequisites :=
      [ { name := "cpa-usage-keeper", kind := .ExecutableOnPath
        , description := "Go binary + embedded npm frontend" }
      , { name := "cpa-usage-keeper.db", kind := .WritableDirectory
        , description := "SQLite store location" }
      , { name := "cpa-usage-keeper dashboard port", kind := .ListeningPort
        , description := "built-in dashboard server" }
      ] }

-- entire (entireio/cli) — captures sessions and links them to code changes
def entire : Plugin :=
  { id := .Custom "entire"
  , version := "0.12.0"
  , description := "CLI tool that captures AI agent sessions and links them to code changes"
  , capabilities := [.SessionCapture, .SessionLinkingToChanges]
  , prerequisites :=
      [ { name := "entire", kind := .ExecutableOnPath
        , description := "Go binary wrapping agent hooks" }
      , { name := "agent hook config", kind := .ConfigDirectory
        , description := "install-time hooks into each agent's session dir" }
      , { name := "git repos", kind := .DataDirectory
        , description := "reads repo history to correlate sessions with commits" }
      ] }

-- mindwalk (cosmtrek) — replays sessions on a 3D map of the codebase
def mindwalk : Plugin :=
  { id := .Custom "mindwalk"
  , version := "0.5.0"
  , description := "Visualization tool that replays coding-agent sessions on a 3D map of your codebase"
  , capabilities := [.SessionReplay, .Dashboard]
  , prerequisites :=
      [ { name := "mindwalk", kind := .ExecutableOnPath
        , description := "Go binary with embedded static frontend" }
      , { name := "session transcripts", kind := .Custom "read set"
        , description := "same agent session roots as agentsview" }
      ] }

-- tokscale (junhoyeo) — token usage analytics CLI/TUI
def tokscale : Plugin :=
  { id := .Custom "tokscale"
  , version := "4.20.1"
  , description := "CLI and TUI for AI token usage analytics"
  , capabilities := [.TokenUsageAnalytics, .CostAccounting]
  , prerequisites :=
      [ { name := "tokscale", kind := .ExecutableOnPath
        , description := "Rust binary; scans agent transcript dirs" }
      , { name := "transcript JSONL roots", kind := .Custom "read set"
        , description := "shared with ccusage" }
      ] }

-- ============================================
-- Registry of all six
-- ============================================

def allPlugins : List Plugin :=
  [agentsview, ccusage, cpaUsageKeeper, entire, mindwalk, tokscale]

-- One negotiation request covering a recovery run: every tool gets probed
def collectionProbeRequest : NegotiationRequest :=
  { id := "probe-agent-telemetry-collection"
  , planned_calls :=
      [ "agentsview --help"
      , "ccusage --help"
      , "cpa-usage-keeper --help"
      , "entire --help"
      , "mindwalk --help"
      , "tokscale --help"
      ]
  , prerequisites := allPlugins.flatMap fun p => p.prerequisites }

-- ============================================
-- Theorems
-- ============================================

-- Six distinct tools are declared
theorem six_plugins : allPlugins.length = 6 := rfl

-- A tool with no declared prerequisites is always supported
theorem trivially_supported (p : Plugin) (h : p.prerequisites = []) (host : Host) :
  prerequisites_supported host p.prerequisites := by
  rw [h]
  rfl

end AgentTelemetry
end Plugins
