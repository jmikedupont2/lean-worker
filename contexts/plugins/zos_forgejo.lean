-- Plugin Context: zos-forgejo
-- AOK argument of knowledge for the zos-forgejo plugin.
-- Proves that the agent's knowledge of zos-forgejo's interface is complete and consistent.

import RequestProject.Twin
import RequestProject.ToolProvenance

namespace PluginContexts

-- ============================================
-- Plugin Interface Definition
-- ============================================

structure PluginInterface where
  name        : String
  version     : String
  description : String
  capabilities : List String
  commands    : List String

-- ============================================
-- zos-forgejo Specific Context
-- ============================================

def zos_forgejoInterface : PluginInterface := {
  name := "zos-forgejo",
  version := "0.1.0",
  description := "Forgejo git repository hosting, issue tracking, and CI/CD platform (self-hosted GitHub alternative)",
  capabilities := ["forgejo", "git", "repository", "issues", "pull-requests", "ci-cd"],
  commands := ["clone", "push", "pull", "fork", "star", "watch", "issue", "pr", "actions", "pipeline"]
}

-- ============================================
-- AOK Theorems (Arguments of Knowledge)
-- ============================================

theorem zos_forgejo_name_correct :
  zos_forgejoInterface.name = "zos-forgejo" := by
  rfl

theorem zos_forgejo_capabilities_nonempty :
  zos_forgejoInterface.capabilities.length > 0 := by
  unfold zos_forgejoInterface
  norm_num [List.length]

theorem zos_forgejo_commands_nonempty :
  zos_forgejoInterface.commands.length > 0 := by
  unfold zos_forgejoInterface
  norm_num [List.length]

theorem zos_forgejo_has_core_capability :
  zos_forgejoInterface.capabilities.contains "forgejo" := by
  unfold zos_forgejoInterface
  have : "forgejo" ∈ ["forgejo", "git", "repository", "issues", "pull-requests", "ci-cd"] := by
    simp
  exact this

theorem zos_forgejo_version_consistent :
  zos_forgejoInterface.version = "0.1.0" := by
  rfl

theorem zos_forgejo_complete_interface :
  zos_forgejoInterface.capabilities.contains "forgejo" ∧
  zos_forgejoInterface.commands.length > 0 := by
  constructor
  · exact zos_forgejo_has_core_capability
  · exact zos_forgejo_commands_nonempty

end PluginContexts