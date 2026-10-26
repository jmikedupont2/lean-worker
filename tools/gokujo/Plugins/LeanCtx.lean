-- LeanCtx.lean
-- lean-ctx plugin for the Gokujo task runner
--
-- lean-ctx gates every shell command through a persistent allowlist
-- (`~/.config/lean-ctx/config.toml`) and serves ctx_* tools over MCP.
-- Blocking is permanent per command until `lean-ctx allow <cmd>` grants it,
-- so the negotiation step must enumerate every binary the task will run.

import Plugins.PluginNegotiation

namespace Plugins
namespace LeanCtx

-- ============================================
-- Plugin declaration
-- ============================================

def plugin : Plugin :=
  { id := .LeanCtx
  , version := "3.10.1"
  , description :=
      "Context-management MCP server: compressed file/search/shell reads " ++
      "plus a persistent shell allowlist that gates command execution"
  , capabilities :=
      [ .ContextCompression
      , .ShellGating
      ]
  , prerequisites :=
      [ { name := "lean-ctx"
        , kind := .ExecutableOnPath
        , description := "CLI + MCP server binary"
        }
      , { name := "~/.config/lean-ctx/config.toml"
        , kind := .ConfigFile
        , description := "Effective roots, allowlist, shell_security policy"
        }
      , { name := "~/.local/state/lean-ctx"
        , kind := .DataDirectory
        , description := "Output-compression tee archives (lossless escape hatches)"
        }
      , { name := "lean-ctx-stdio"
        , kind := .Custom "MCP stdio transport"
        , description := "ctx_* tool surface; 63 tools exposed"
        }
      ]
  }

-- ============================================
-- Allowlist grants a task must negotiate
-- ============================================

-- One allowlist prerequisite per binary the agent plans to exec
def allowPrereq (cmd : String) : Prerequisite :=
  { name := cmd
  , kind := .ShellAllowlistEntry
  , description := s!"lean-ctx shell allowlist entry for `{cmd}`"
  }

-- The negotiation request the tmux-recovery task needed (2026-10-24):
-- six llm-agents tools blocked mid-run because the allowlist was resolved
-- lazily instead of during task negotiation.
def llmAgentsToolsRequest : NegotiationRequest :=
  { id := "run-llm-agents-tools"
  , planned_calls :=
      [ "agentsview --help"
      , "ccusage --help"
      , "cpa-usage-keeper --help"
      , "entire --help"
      , "mindwalk --help"
      , "tokscale --help"
      ]
  , prerequisites :=
      List.map allowPrereq
        ["agentsview", "ccusage", "cpa-usage-keeper", "entire", "mindwalk", "tokscale"] ++
      [ { name := "lean"
        , kind := .ShellAllowlistEntry
        , description := "type-check standalone Lean files"
        }
      , { name := "lake"
        , kind := .ShellAllowlistEntry
        , description := "build the gokujo/lake project"
        }
      ]
  }

-- Recovery from a permanent block: either the allow entry or relax gating.
-- Modeled as the two repairs the tool itself prints on denial.
def blockRepairChoices (cmd : String) : List String :=
  [ s!"lean-ctx allow {cmd}"
  , "set shell_security = \"off\" in ~/.config/lean-ctx/config.toml (user's call)"
  ]

-- ============================================
-- Theorems
-- ============================================

-- The negotiated request is only granted when every binary is allowlisted
-- (i.e. shows up as available on the probed host).
theorem negotiate_granted_implies_supported
  (host : Host) (req : NegotiationRequest)
  (h : negotiate host req = .granted) :
  prerequisites_supported host req.prerequisites := by
  -- unmet = [] ⟹ every prereq available; needs List.filter_eq_nil_iff
  sorry

theorem llm_agents_request_supported_needs_all
  (host : Host)
  (h : negotiate host llmAgentsToolsRequest = .granted) :
  prerequisites_supported host llmAgentsToolsRequest.prerequisites :=
  negotiate_granted_implies_supported host llmAgentsToolsRequest h

-- ============================================
-- Worked demo (2026-10-24 outage → 2026-10-25 repair)
-- ============================================

-- The host as probed on 2026-10-24: lean/lake already allowlisted, the six
-- llm-agents tools not.
def hostOct24 : Host :=
  { emptyHost with
    allowlisted_cmds := ["lean", "lake"]
  , executables_on_path := ["lean", "lake"]
  }

-- After `lean-ctx allow` ×6 (2026-10-25), from the live config dump.
def hostAfterRepair : Host :=
  { emptyHost with
    allowlisted_cmds :=
      ["agentsview", "ccusage", "cpa-usage-keeper", "entire", "mindwalk",
       "tokscale", "lean", "lake"]
  , executables_on_path :=
      ["agentsview", "ccusage", "entire", "mindwalk", "lean", "lake"]
  }

-- Blocked on 2026-10-24, on exactly the six missing binaries — the outage
-- was predictable, the missing set is computable before dispatch:
theorem demo_blocked_exactly_the_six :
    List.map (fun p => p.name)
      (unmet hostOct24 llmAgentsToolsRequest.prerequisites) =
      ["agentsview", "ccusage", "cpa-usage-keeper", "entire", "mindwalk",
       "tokscale"] := by decide

theorem demo_blocked_before_repair :
    negotiate hostOct24 llmAgentsToolsRequest ≠ .granted := by decide

-- Granted after the repair: `lean-ctx allow` ×6 flipped negotiation.
theorem demo_granted_after_repair :
    negotiate hostAfterRepair llmAgentsToolsRequest = .granted := by decide

end LeanCtx
end Plugins
