-- RequestProject/PluginContexts.lean
-- RequestProject library root for Gokujo onboarding tool plugins.
--
-- Every dedicated tool for the lean-worker onboarding workflow carries a
-- PluginContext module in this directory.  The module name is the
-- `interface_module` path used by lean_worker_registry.lean and
-- contexts/registry/registry.json so that lean_worker_main can map a registered
-- tool to its Lean4 context without a runtime reflection layer.
--
-- Layout per tool:
--   RequestProject/PluginContexts/<tool>.lean
--     namespace RequestProject.PluginContexts
--     structure PluginInterface { name, version, description, capabilities, commands }
--     def <tool>Interface : PluginInterface
--     AOK theorems: <tool>_name_correct, <tool>_capabilities_nonempty, ...
--     end PluginContexts
--
-- This file replaces the old single flat namespace
-- `minimal/lean_worker_registry.lean` (`namespace PluginContexts`) in the
-- lean-worker registry.  The registry now imports the per-tool modules instead
-- of carrying all bodies inline.

namespace RequestProject.PluginContexts

-- Placeholder declaration; every real plugin module is defined in this
-- directory and imported here.  Do not add module bodies here.
def _placeholder : Nat := 0

end RequestProject.PluginContexts
