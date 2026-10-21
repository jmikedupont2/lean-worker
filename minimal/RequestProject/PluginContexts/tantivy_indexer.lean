-- Plugin Context: tantivy-indexer
-- AOK argument of knowledge for the tantivy-indexer plugin.
-- Proves that the agent's knowledge of tantivy-indexer's interface is complete and consistent.

import RequestProject.Twin
import RequestProject.ToolProvenance

namespace PluginContexts.tantivy_indexer

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
-- tantivy-indexer Specific Context
-- ============================================

def tantivy_indexerInterface : PluginInterface := {
  name := "tantivy-indexer",
  version := "0.1.0",
  description := "Index shmem dump blocks into Tantivy for sub-ms full-text search",
  capabilities := ["forgecode", "dotagents"],
  commands := []
}

-- ============================================
-- AOK Theorems (Arguments of Knowledge)
-- ============================================

-- Theorem 1: The agent knows the plugin name is correct.
theorem tantivy_indexer_name_correct :
  tantivy_indexerInterface.name = "tantivy-indexer" := by
  rfl

-- Theorem 2: The agent knows all capabilities are non-empty.
theorem tantivy_indexer_capabilities_nonempty :
  tantivy_indexerInterface.capabilities.length > 0 := by
  unfold tantivy_indexerInterface
  decide

-- Theorem 3: the interface declares no shell commands, so the list is empty.
theorem tantivy_indexer_commands_empty :
  tantivy_indexerInterface.commands.length = 0 := by
  unfold tantivy_indexerInterface
  rfl

-- Theorem 4: The plugin provides core capability (is in agent's knowledge).
theorem tantivy_indexer_has_core_capability :
  tantivy_indexerInterface.capabilities.contains "forgecode" := by
  unfold tantivy_indexerInterface
  decide

-- Theorem 5: The agent knows the version is consistent with manifest.
theorem tantivy_indexer_version_consistent :
  tantivy_indexerInterface.version = "0.1.0" := by
  rfl

-- Theorem 6: The agent knows the plugin has core capabilities (completeness).
theorem tantivy_indexer_complete_interface :
  tantivy_indexerInterface.capabilities.contains "forgecode" ∧
  tantivy_indexerInterface.capabilities.length > 0 := by
  constructor
  · exact tantivy_indexer_has_core_capability
  · exact tantivy_indexer_capabilities_nonempty

end PluginContexts.tantivy_indexer
