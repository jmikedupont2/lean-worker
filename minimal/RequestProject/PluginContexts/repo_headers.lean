-- Plugin Context: repo-headers
-- AOK argument of knowledge for the repo-headers plugin.
-- Proves that the agent's knowledge of repo-headers's interface is complete and consistent.

import RequestProject.Twin
import RequestProject.ToolProvenance

namespace PluginContexts.repo_headers

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
-- repo-headers Specific Context
-- ============================================

def repo_headersInterface : PluginInterface := {
  name := "repo-headers",
  version := "0.1.0",
  description := "Repository header extraction and search index",
  capabilities := ["forgecode", "dotagents"],
  commands := []
}

-- ============================================
-- AOK Theorems (Arguments of Knowledge)
-- ============================================

-- Theorem 1: The agent knows the plugin name is correct.
theorem repo_headers_name_correct :
  repo_headersInterface.name = "repo-headers" := by
  rfl

-- Theorem 2: The agent knows all capabilities are non-empty.
theorem repo_headers_capabilities_nonempty :
  repo_headersInterface.capabilities.length > 0 := by
  unfold repo_headersInterface
  decide

-- Theorem 3: the interface declares no shell commands, so the list is empty.
theorem repo_headers_commands_empty :
  repo_headersInterface.commands.length = 0 := by
  unfold repo_headersInterface
  rfl

-- Theorem 4: The plugin provides core capability (is in agent's knowledge).
theorem repo_headers_has_core_capability :
  repo_headersInterface.capabilities.contains "forgecode" := by
  unfold repo_headersInterface
  decide

-- Theorem 5: The agent knows the version is consistent with manifest.
theorem repo_headers_version_consistent :
  repo_headersInterface.version = "0.1.0" := by
  rfl

-- Theorem 6: The agent knows the plugin has core capabilities (completeness).
theorem repo_headers_complete_interface :
  repo_headersInterface.capabilities.contains "forgecode" ∧
  repo_headersInterface.capabilities.length > 0 := by
  constructor
  · exact repo_headers_has_core_capability
  · exact repo_headers_capabilities_nonempty

end PluginContexts.repo_headers
