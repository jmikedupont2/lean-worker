-- Worker Tool Binding Module
-- Maps plugin contexts to aristotle-manager commands
-- Provides GOAP task planning interface

import PluginContexts
import RequestProject.Twin
import RequestProject.ToolProvenance

namespace WorkerToolBinding

-- ============================================
-- Aristotle-Manager Command Definitions
-- ============================================

structure Command where
  name        : String
  description : String
  args        : List String
  envVars     : List String

-- ============================================
-- Worker Description Structure
-- ============================================

structure WorkerDescription where
  name         : String
  description  : String
  commands     : List Command
  capabilities : List String
  permissions  : List String

-- ============================================
-- GOAP Task Planning Interface
-- ============================================

structure TaskState where
  projectExists   : Bool
  apiKeyAvailable : Bool
  indexBuilt      : Bool
  projectBuilt    : Bool
  projectDeployed : Bool

structure TaskAction where
  name        : String
  preconditions : TaskState
  effects       : TaskState

-- ============================================
-- Command Mappings by Plugin Context
-- ============================================

def getAristotleManagerCommand (pluginName : String) : Option Command :=
  match pluginName with
  | "aristotle_manager" => some {
      name := "poll",
      description := "Poll for new projects from Aristotle API",
      args := ["--download-only", "--parallel"],
      envVars := ["ARISTOTLE_API_KEY"]
    }
  | "aristotle_manager" => some {
      name := "build",
      description := "Build all projects",
      args := ["--input-dir"],
      envVars := []
    }
  | "aristotle_manager" => some {
      name := "download",
      description := "Download results from Aristotle",
      args := ["--parallel", "--verbose"],
      envVars := ["ARISTOTLE_API_KEY"]
    }
  | "aristotle_manager" => some {
      name := "search",
      description := "Search project database",
      args := ["--query", "--limit"],
      envVars := []
    }
  | "aristotle_manager" => some {
      name := "deploy",
      description := "Deploy project to Cloudflare Pages",
      args := ["--cloudflare", "--name", "--public"],
      envVars := ["CLOUDFLARE_API_TOKEN", "CLOUDFLARE_ACCOUNT_ID"]
    }
  | "aristotle_manager" => some {
      name := "search-index",
      description := "Build tantivy index from aristotle_projects.json",
      args := ["--json", "--output"],
      envVars := []
    }
  | "aristotle_manager" => some {
      name := "enrich",
      description := "Run task-enricher + GOAP pipeline",
      args := ["--project-id", "--skip-task-enricher", "--skip-goap"],
      envVars := []
    }
  | "aristotle_manager" => some {
      name := "term-graph",
      description := "Build term graph",
      args := ["--git-base", "--output-dir"],
      envVars := []
    }
  | "aristotle_manager" => some {
      name := "project-test",
      description := "Run project tests",
      args := ["--mode", "--iterations", "--timeout"],
      envVars := []
    }
  | _ => none

-- ============================================
-- Worker Binding Definitions
-- ============================================

def aristotleManagerBinding : WorkerDescription where
  name := "aristotle-manager"
  description := "Aristotle API client — poll, download, build, split, merge, index Lean projects"
  commands := [
    { name := "poll", description := "Poll for new projects", args := ["--download-only", "--parallel"], envVars := ["ARISTOTLE_API_KEY"] },
    { name := "build", description := "Build all projects", args := ["--input-dir"], envVars := [] },
    { name := "download", description := "Download results from Aristotle", args := ["--parallel", "--verbose"], envVars := ["ARISTOTLE_API_KEY"] },
    { name := "search", description := "Search project database", args := ["--query", "--limit"], envVars := [] },
    { name := "deploy", description := "Deploy to Cloudflare Pages", args := ["--cloudflare", "--name", "--public"], envVars := ["CLOUDFLARE_API_TOKEN", "CLOUDFLARE_ACCOUNT_ID"] },
    { name := "search-index", description := "Build tantivy index", args := ["--json", "--output"], envVars := [] },
    { name := "enrich", description := "Run task-enricher + GOAP pipeline", args := ["--project-id", "--skip-task-enricher", "--skip-goap"], envVars := [] },
    { name := "term-graph", description := "Build term graph", args := ["--git-base", "--output-dir"], envVars := [] },
    { name := "project-test", description := "Run project tests", args := ["--mode", "--iterations", "--timeout"], envVars := [] }
  ]
  capabilities := ["forgecode", "dotagents"]
  permissions := ["read", "write", "execute", "deploy"]

-- ============================================
-- GOAP Task Plans
-- ============================================

def planBuildProject : List TaskAction := [
  { name := "poll", preconditions := { projectExists := false, apiKeyAvailable := true, indexBuilt := false, projectBuilt := false, projectDeployed := false }, effects := { projectExists := true, apiKeyAvailable := true, indexBuilt := false, projectBuilt := false, projectDeployed := false } },
  { name := "build", preconditions := { projectExists := true, apiKeyAvailable := true, indexBuilt := false, projectBuilt := false, projectDeployed := false }, effects := { projectExists := true, apiKeyAvailable := true, indexBuilt := true, projectBuilt := true, projectDeployed := false } },
  { name := "deploy", preconditions := { projectExists := true, apiKeyAvailable := true, indexBuilt := true, projectBuilt := true, projectDeployed := false }, effects := { projectExists := true, apiKeyAvailable := true, indexBuilt := true, projectBuilt := true, projectDeployed := true } }
]

def planSearchAndDeploy : List TaskAction := [
  { name := "search-index", preconditions := { projectExists := true, apiKeyAvailable := true, indexBuilt := false, projectBuilt := false, projectDeployed := false }, effects := { projectExists := true, apiKeyAvailable := true, indexBuilt := true, projectBuilt := false, projectDeployed := false } },
  { name := "search", preconditions := { projectExists := true, apiKeyAvailable := true, indexBuilt := true, projectBuilt := false, projectDeployed := false }, effects := { projectExists := true, apiKeyAvailable := true, indexBuilt := true, projectBuilt := false, projectDeployed := false } },
  { name := "deploy", preconditions := { projectExists := true, apiKeyAvailable := true, indexBuilt := true, projectBuilt := true, projectDeployed := false }, effects := { projectExists := true, apiKeyAvailable := true, indexBuilt := true, projectBuilt := true, projectDeployed := true } }
]

-- ============================================
-- Task Runner Integration Interface
-- ============================================

structure TaskRunnerInterface where
  name        : String
  description : String
  capabilities : List String
  tools        : List Command

def taskRunnerBinding : TaskRunnerInterface where
  name := "task-runner"
  description := "Task runner server for lean-worker"
  capabilities := ["task-planning", "execution", "monitoring", "sops-integration"]
  tools := [
    { name := "sops-decrypt", description := "Decrypt sops vault", args := ["--key-file", "--secret-name"], envVars := ["SOPS_AGE_KEY_FILE"] },
    { name := "sops-encrypt", description := "Encrypt to sops vault", args := ["--key-file", "--secret-name"], envVars := ["SOPS_AGE_KEY_FILE"] },
    { name := "systemd-run", description := "Run task via systemd", args := ["--service", "--user"], envVars := [] },
    { name := "lean4-prove", description := "Prove permissions in Lean4", args := ["--module", "--goal"], envVars := [] }
  ]

-- ============================================
-- SOPS Integration for Key Management
-- ============================================

structure SopsConfig where
  vaultDir     : String
  keyFile      : String
  recipientsFile : String

def sopsConfig : SopsConfig where
  vaultDir := "/etc/tracker-vault"
  keyFile := "/etc/tracker-vault/vault.key"
  recipientsFile := "/etc/tracker-vault/vault.pub"

-- ============================================
-- Systemd Integration
-- ============================================

structure SystemdService where
  name       : String
  description : String
  execStart  : String
  environment : List (String × String)
  permissions : List String

def leanWorkerService : SystemdService where
  name := "lean-worker"
  description := "Lean4 Worker Service with SOPS integration"
  execStart := "/home/mdupont/projects/lean-worker/minimal/gokujo"
  environment := [
    ("GUI2PROOF_RUNTIME_ENV", "/run/gui2proof/cloudflare.env"),
    ("SOPS_AGE_KEY_FILE", "/etc/tracker-vault/vault.key"),
    ("GUI2PROOF_CLOUDFLARE_SECRET", "cloudflare-pages-token")
  ]
  permissions := ["network", "filesystem-read", "filesystem-write", "systemd-managed"]

-- ============================================
-- Permission Calculation and Proof
-- ============================================

structure PermissionSet where
  read    : Bool
  write   : Bool
  execute : Bool
  deploy  : Bool
  network : Bool
  manage  : Bool

def calculatePermissions (service : SystemdService) : PermissionSet :=
  { read := true, write := true, execute := true, deploy := true, network := true, manage := true }

theorem permissions_calculated :
  calculatePermissions leanWorkerService = { read := true, write := true, execute := true, deploy := true, network := true, manage := true } := by
  rfl

end WorkerToolBinding
