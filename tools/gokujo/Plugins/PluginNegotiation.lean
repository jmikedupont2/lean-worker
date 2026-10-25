-- PluginNegotiation.lean
-- Task-runner plugin negotiation for Gokujo
--
-- A task declares the plugins (tools, skills) its agent needs; each plugin
-- declares prerequisites (executables, allowlist entries, data directories,
-- ports, configs). Negotiation resolves every prerequisite up-front, before
-- the task runs, so the agent is never blocked mid-execution by a missing
-- permission.

namespace Plugins

-- ============================================
-- Prerequisites
-- ============================================

-- Kind of prerequisite a plugin needs from the host
inductive PrerequisiteKind
  | ExecutableOnPath
  | ShellAllowlistEntry
  | ConfigFile
  | ConfigDirectory
  | DataDirectory
  | WritableDirectory
  | NetworkAccess
  | ListeningPort
  | SystemdUnit
  | SecretEnvVar
  | Custom (of : String)
  deriving Repr, DecidableEq

-- Single prerequisite declaration
structure Prerequisite where
  name : String
  kind : PrerequisiteKind
  description : String
  deriving Repr, DecidableEq

-- Host facts gathered by probing the machine
structure Host where
  executables_on_path : List String
  allowlisted_cmds : List String
  readable_dirs : List String
  writable_dirs : List String
  running_services : List String
  env_vars : List String
  deriving Repr, DecidableEq

def emptyHost : Host :=
  { executables_on_path := []
  , allowlisted_cmds := []
  , readable_dirs := []
  , writable_dirs := []
  , running_services := []
  , env_vars := []
  }

-- Is one prerequisite satisfied by the host?
def is_available (host : Host) (name : String) : Bool :=
  name ∈ host.executables_on_path ||
  name ∈ host.allowlisted_cmds ||
  name ∈ host.readable_dirs ||
  name ∈ host.writable_dirs ||
  name ∈ host.running_services ||
  name ∈ host.env_vars

-- Prerequisites that the host cannot satisfy
def unmet (host : Host) (prereqs : List Prerequisite) : List Prerequisite :=
  prereqs.filter fun p => !is_available host p.name

-- Are all prerequisites satisfied?
def prerequisites_supported (host : Host) (prereqs : List Prerequisite) : Bool :=
  prereqs.all fun p => is_available host p.name

-- ============================================
-- Negotiation
-- ============================================

-- Outcome of negotiating one unit of work
inductive NegotiationOutcome
  | granted
  | granted_with_work
  | denied (reason : String)
  | blocked (missing : List Prerequisite)
  deriving Repr, DecidableEq

-- A unit of work: the agent's planned calls plus what it must have
structure NegotiationRequest where
  id : String
  planned_calls : List String
  prerequisites : List Prerequisite
  deriving Repr, DecidableEq

-- Task body: named, owned by one plugin
structure TaskBody where
  name : String
  plugin : String
  requests : List NegotiationRequest
  deriving Repr, DecidableEq

-- Negotiate one request against the host
def negotiate (host : Host) (req : NegotiationRequest) : NegotiationOutcome :=
  let u := unmet host req.prerequisites
  if req.planned_calls.isEmpty then
    .denied "nothing to run — no planned calls"
  else if u.isEmpty then
    .granted
  else
    .blocked u

-- Negotiate a whole task before it may start
def negotiateTask (host : Host) (task : TaskBody) : List (String × NegotiationOutcome) :=
  task.requests.map fun req => (req.id, negotiate host req)

-- A task is runnable only when every request is granted outright
def task_supported (host : Host) (task : TaskBody) : Bool :=
  task.requests.all fun req =>
    (negotiate host req) == NegotiationOutcome.granted

-- ============================================
-- Plugin declaration
-- ============================================

-- Identity of a plugin as registered with the task runner
inductive PluginId
  | LeanCtx
  | AgentTelemetry
  | Custom (of : String)
  deriving Repr, DecidableEq

-- What a plugin contributes
inductive PluginCapability
  | ContextCompression
  | ShellGating
  | SessionCapture
  | TokenUsageAnalytics
  | CostAccounting
  | SessionReplay
  | SessionLinkingToChanges
  | Dashboard
  | Custom (of : String)
  deriving Repr, DecidableEq

-- Declared plugin: capabilities plus the negotiation payload it requires
structure Plugin where
  id : PluginId
  version : String
  description : String
  capabilities : List PluginCapability
  prerequisites : List Prerequisite
  deriving Repr, DecidableEq

structure PluginRegistry where
  plugins : List Plugin
  host : Host
  deriving Repr

def registerPlugin (registry : PluginRegistry) (plugin : Plugin) : PluginRegistry :=
  { registry with plugins := registry.plugins ++ [plugin] }

def plugins_supported (registry : PluginRegistry) : List Plugin :=
  registry.plugins.filter fun p => prerequisites_supported registry.host p.prerequisites

def unsupported_prerequisites (registry : PluginRegistry) : List Prerequisite :=
  registry.plugins.flatMap fun p => unmet registry.host p.prerequisites

-- ============================================
-- Theorems
-- ============================================

-- A request with no planned calls is never granted
theorem negotiate_empty_calls_not_granted
  (host : Host) (prereqs : List Prerequisite) :
  negotiate host { id := "t", planned_calls := [], prerequisites := prereqs } ≠
    NegotiationOutcome.granted := by
  unfold negotiate
  simp

-- A supported plugin has no unmet prerequisites
theorem supported_plugin_has_no_unmet
  (host : Host) (plugin : Plugin)
  (h : prerequisites_supported host plugin.prerequisites) :
  unmet host plugin.prerequisites = [] := by
  unfold unmet
  simp [prerequisites_supported] at h ⊢
  omega

-- Negotiation is deterministic: same host and request, same outcome
theorem negotiate_deterministic
  (host : Host) (req : NegotiationRequest) :
  negotiate host req = negotiate host req := rfl

end Plugins
