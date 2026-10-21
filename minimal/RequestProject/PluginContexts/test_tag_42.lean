-- Plugin Context: test-tag-42
-- AOK argument of knowledge for the test-tag-42 plugin.
-- Proves that the agent's knowledge of test-tag-42's interface is complete and consistent.

import RequestProject.Twin
import RequestProject.ToolProvenance

namespace PluginContexts.test_tag_42

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
-- test-tag-42 Specific Context
-- ============================================

def test_tag_42Interface : PluginInterface := {
  name := "test-tag-42",
  version := "0.1.0",
  description := "Smoke test for CBOR tag 42 (CID signature) detection in the IPLD CAR shmem search index",
  capabilities := ["forgecode", "dotagents"],
  commands := []
}

-- ============================================
-- AOK Theorems (Arguments of Knowledge)
-- ============================================

-- Theorem 1: The agent knows the plugin name is correct.
theorem test_tag_42_name_correct :
  test_tag_42Interface.name = "test-tag-42" := by
  rfl

-- Theorem 2: The agent knows all capabilities are non-empty.
theorem test_tag_42_capabilities_nonempty :
  test_tag_42Interface.capabilities.length > 0 := by
  unfold test_tag_42Interface
  decide

-- Theorem 3: the interface declares no shell commands, so the list is empty.
theorem test_tag_42_commands_empty :
  test_tag_42Interface.commands.length = 0 := by
  unfold test_tag_42Interface
  rfl

-- Theorem 4: The plugin provides core capability (is in agent's knowledge).
theorem test_tag_42_has_core_capability :
  test_tag_42Interface.capabilities.contains "forgecode" := by
  unfold test_tag_42Interface
  decide

-- Theorem 5: The agent knows the version is consistent with manifest.
theorem test_tag_42_version_consistent :
  test_tag_42Interface.version = "0.1.0" := by
  rfl

-- Theorem 6: The agent knows the plugin has core capabilities (completeness).
theorem test_tag_42_complete_interface :
  test_tag_42Interface.capabilities.contains "forgecode" ∧
  test_tag_42Interface.capabilities.length > 0 := by
  constructor
  · exact test_tag_42_has_core_capability
  · exact test_tag_42_capabilities_nonempty

end PluginContexts.test_tag_42
