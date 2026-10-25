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
-- Probed 2026-10-25: indexed 38 sessions from Oct 23-25 across 8 agents
-- (qoder, pi, kilo, codex, opencode, freebuff, hermes + cline-family);
-- watches 117 roots / 2652 dirs; sync daemon left one "worker pass failed"
-- diagnostic but health/projects/export all answered.
def agentsview : Plugin :=
  { id := .Custom "agentsview"
  , version := "0.45.0"
  , description := "Local-first viewer and analytics for AI coding agent sessions; SQLite archive at ~/.agentsview/sessions.db with export + MCP read tools"
  , capabilities := [.SessionCapture, .SessionReplay, .Dashboard]
  , prerequisites :=
      [ { name := "agentsview", kind := .ExecutableOnPath
        , description := "Go binary on PATH via nix profile; also ships a systemd unit" }
      , { name := "~/.agentsview", kind := .WritableDirectory
        , description := "sessions.db + serve.log — created on first sync" }
      , { name := "agent session roots", kind := .Custom "read set"
        , description := "probed: ~/.pi/agent/sessions, ~/.qoder/logs, ~/.codex, ~/.gemini, ~/.cursor, ~/.claude/projects, ~/.local/share/{opencode,kilo,agent-deck}, ~/.letta — 117 roots watched" }
      , { name := "agentsview serve port", kind := .ListeningPort
        , description := "probed: 8080, falls back to 8084 when busy" }
      ] }

-- ccusage (ccusage/rust) — token + cost analytics from local JSONL
-- Probed 2026-10-25: 18 per-agent subcommands (daily/monthly/weekly/session
-- for claude, codex, opencode, pi, kilo, hermes, ...). Costed the Oct 23-25
-- window at ~325M tokens / $0.79. No qoder parser; warns on unpribed
-- openrouter/free models. Stateless — re-reads transcripts every call.
def ccusage : Plugin :=
  { id := .Custom "ccusage"
  , version := "20.0.40"
  , description := "Analyze coding agent CLI token usage and costs from local data; per-agent subcommands incl. pi, kilo, hermes, opencode"
  , capabilities := [.TokenUsageAnalytics, .CostAccounting]
  , prerequisites :=
      [ { name := "ccusage", kind := .ExecutableOnPath
        , description := "Rust binary reading agent transcript JSONL" }
      , { name := "transcript JSONL roots", kind := .Custom "read set"
        , description := "probed: same per-agent dirs; no write state" }
      ] }

-- cpa-usage-keeper (Willxup) — CliProxyAPI usage tracker
-- Probed 2026-10-25: server-only binary (-env/-host flags); requires a
-- CliProxyAPI deployment. None on this host -> collects nothing here.
def cpaUsageKeeper : Plugin :=
  { id := .Custom "cpa-usage-keeper"
  , version := "2.0.0"
  , description := "Standalone CliProxyAPI usage tracker with SQLite persistence and dashboard"
  , capabilities := [.CostAccounting, .Dashboard]
  , prerequisites :=
      [ { name := "cpa-usage-keeper", kind := .ExecutableOnPath
        , description := "Go binary + embedded npm frontend (nix build succeeded)" }
      , { name := "cli-proxy-api deployment", kind := .Custom "upstream service"
        , description := "probed 2026-10-25: absent on this host — plugin unsupported until a cpa instance exists" }
      , { name := "cpa-usage-keeper.db", kind := .WritableDirectory
        , description := "SQLite store location" }
      ] }

-- entire (entireio/cli) — captures sessions and links them to code changes
-- Probed 2026-10-25: opt-in per repository (`entire status` -> "not set up"
-- in lean-worker; no ~/.entire on this host). Collects nothing retroactively;
-- forward-looking capture + checkpoint/commit linking only after
-- `entire enable` + `entire agent add`.
def entire : Plugin :=
  { id := .Custom "entire"
  , version := "0.12.0"
  , description := "CLI tool that captures AI agent sessions and links them to code changes"
  , capabilities := [.SessionCapture, .SessionLinkingToChanges]
  , prerequisites :=
      [ { name := "entire", kind := .ExecutableOnPath
        , description := "Go binary wrapping agent hooks" }
      , { name := "enabled repository", kind := .Custom "opt-in state"
        , description := "probed 2026-10-25: no repo here runs `entire enable`; negotiation must deny retroactive recovery" }
      , { name := "git repos", kind := .DataDirectory
        , description := "reads repo history to correlate sessions with commits" }
      ] }

-- mindwalk (cosmtrek) — replays sessions on a 3D map of the codebase
-- Probed 2026-10-25: subcommands serve/open/map/build/trace/analyze;
-- serve flags --claude-dir, --codex-dir, --pi-dir — the pi session tree
-- (~3000 JSONL here) is directly replayable. analyze shells out to a
-- local judge CLI (claude|codex).
def mindwalk : Plugin :=
  { id := .Custom "mindwalk"
  , version := "0.5.0"
  , description := "Visualization tool that replays coding-agent sessions on a 3D map of your codebase"
  , capabilities := [.SessionReplay, .Dashboard]
  , prerequisites :=
      [ { name := "mindwalk", kind := .ExecutableOnPath
        , description := "Go binary with embedded static frontend" }
      , { name := "~/.pi/agent/sessions", kind := .DataDirectory
        , description := "probed: --pi-dir source (also --claude-dir, --codex-dir)" }
      , { name := "judge cli", kind := .Custom "optional subprocess"
        , description := "`analyze` invokes claude or codex CLI; gated by lean-ctx allowlist" }
      ] }

-- tokscale (junhoyeo) — token usage analytics CLI/TUI
-- Probed 2026-10-25: `clients` reports per-client roots — opencode 15.7K
-- msgs (~/.local/share/opencode/storage/message), gemini 34.9K
-- (~/.gemini/tmp), codex 8.2K (~/.codex/sessions, 29/74 rollouts lack usage
-- records), droid (~/.factory/sessions), cursor/amp via cache dirs. First
-- full scan took >10 min; aggregates incl. mistral-vibe at $794.17.
def tokscale : Plugin :=
  { id := .Custom "tokscale"
  , version := "4.20.1"
  , description := "CLI and TUI for AI token usage analytics"
  , capabilities := [.TokenUsageAnalytics, .CostAccounting]
  , prerequisites :=
      [ { name := "tokscale", kind := .ExecutableOnPath
        , description := "Rust binary; not on PATH here — resolved via nix store path" }
      , { name := "~/.config/tokscale", kind := .WritableDirectory
        , description := "probed: settings, headless roots, cursor/amp caches" }
      , { name := "agent transcript roots", kind := .Custom "read set"
        , description := "probed via `clients`: opencode/gemini/codex/droid/claude trees; no pi/kilo/qoder client" }
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
