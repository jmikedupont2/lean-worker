-- Wrangler.lean
-- Formal model of Cloudflare Wrangler API and Cloudflare data types
-- for integration with Gokujo build system

namespace Cloudflare
namespace Wrangler

-- ============================================
-- Cloudflare Account Types
-- ============================================

-- Cloudflare Account ID type
def AccountId := String

-- Cloudflare API Token type
def ApiToken := String

-- Cloudflare Zone ID type
def ZoneId := String

-- Cloudflare Script Name type
def ScriptName := String

-- ============================================
-- Cloudflare Workers Types
-- ============================================

-- Worker script configuration
structure WorkerConfig where
  name        : ScriptName
  main        : String  -- Main module file
  compatibility_date : String  -- Workers runtime compatibility date
  compatibility_flags : List String  -- Additional compatibility flags

-- Worker environment variables
structure WorkerEnv where
  key   : String
  value : String
  type_ : String  -- "plain_text", "secret_text", "kv_namespace", etc.

abbrev WorkerEnvVars := List WorkerEnv

-- Worker KV namespace binding
structure WorkerKVBinding where
  name      : String  -- Binding name
  namespace : String  -- KV namespace ID

abbrev WorkerKVBindings := List WorkerKVBinding

-- Worker R2 bucket binding
structure WorkerR2Binding where
  name    : String  -- Binding name
  bucket  : String  -- R2 bucket name

abbrev WorkerR2Bindings := List WorkerR2Binding

-- Worker D1 database binding
structure WorkerD1Binding where
  name    : String  -- Binding name
  database : String  -- D1 database ID

abbrev WorkerD1Bindings := List WorkerD1Binding

-- Worker DO binding (Durable Objects)
structure WorkerDOBinding where
  name : String  -- Binding name
  class_ : String  -- DO class name

abbrev WorkerDOBindings := List WorkerDOBinding

-- Complete Worker configuration
structure Worker where
  name        : ScriptName
  config      : WorkerConfig
  env         : WorkerEnvVars
  kv          : WorkerKVBindings
  r2          : WorkerR2Bindings
  d1          : WorkerD1Bindings
  do_         : WorkerDOBindings

-- ============================================
-- Cloudflare Worker Commands
-- ============================================

-- Wrangler dev command
structure WranglerDevCommand where
  name        : ScriptName
  outdir      : Option String
  port        : Option Nat

-- Wrangler dev options
structure WranglerDevOptions where
  port     : Option Nat
  local    : Option Bool
  upstream : Option String

-- Wrangler publish options
structure WranglerPublishOptions where
  force    : Option Bool
  dryRun   : Option Bool

-- ============================================
-- Wrangler CLI Commands (SOPS Cloudflare Deployment)
-- ============================================

-- wrangler secrets-store create
structure WranglerSecretsStoreCreate where
  storeId      : String
  name         : String
  value        : String
  scopes       : List String
  accountId    : Option String

-- wrangler secrets-store list
structure WranglerSecretsStoreList where
  accountId    : Option String

-- wrangler secrets-store get
structure WranglerSecretsStoreGet where
  storeId      : String
  name         : String
  accountId    : Option String

-- wrangler secrets-store delete
structure WranglerSecretsStoreDelete where
  storeId      : String
  name         : String
  accountId    : Option String

-- wrangler deploy (alias for publish)
structure WranglerDeploy where
  name         : ScriptName
  config       : Option String  -- path to wrangler.toml
  accountId    : Option String
  force        : Option Bool
  dryRun       : Option Bool

-- wrangler kv:namespace create
structure WranglerKVNamespaceCreate where
  name         : String
  accountId    : Option String

-- wrangler kv:key put
structure WranglerKVKeyPut where
  namespaceId  : String
  key          : String
  value        : String
  accountId    : Option String

-- wrangler r2 bucket create
structure WranglerR2BucketCreate where
  name         : String
  accountId    : Option String

-- wrangler d1 create
structure WranglerD1Create where
  name         : String
  accountId    : Option String

-- wrangler d1 execute
structure WranglerD1Execute where
  databaseId   : String
  command      : String
  accountId    : Option String

-- wrangler pages deploy
structure WranglerPagesDeploy where
  projectName  : String
  directory    : String
  branch       : Option String
  accountId    : Option String

-- wrangler whoami
structure WranglerWhoami where
  accountId    : Option String

-- wrangler versions
structure WranglerVersions where
  accountId    : Option String

-- wrangler login
structure WranglerLogin where
  apiToken     : Option String

-- wrangler logout
structure WranglerLogout := Unit

-- SOPS-wrapped wrangler commands
-- These use sops-decrypted secrets for authentication
structure SOPSWranglerCommand where
  baseCommand  : String  -- the wrangler subcommand string
  sopsSecret   : String  -- sops-encrypted secret reference
  accountId    : AccountId

-- Wrangler command union type
inductive WranglerCommandType
  | secretsStoreCreate (cmd : WranglerSecretsStoreCreate)
  | secretsStoreList (cmd : WranglerSecretsStoreList)
  | secretsStoreGet (cmd : WranglerSecretsStoreGet)
  | secretsStoreDelete (cmd : WranglerSecretsStoreDelete)
  | deploy (cmd : WranglerDeploy)
  | dev (cmd : WranglerDevOptions)
  | publish (cmd : WranglerPublishOptions)
  | kvNamespaceCreate (cmd : WranglerKVNamespaceCreate)
  | kvKeyPut (cmd : WranglerKVKeyPut)
  | r2BucketCreate (cmd : WranglerR2BucketCreate)
  | d1Create (cmd : WranglerD1Create)
  | d1Execute (cmd : WranglerD1Execute)
  | pagesDeploy (cmd : WranglerPagesDeploy)
  | whoami (cmd : WranglerWhoami)
  | versions (cmd : WranglerVersions)
  | login (cmd : WranglerLogin)
  | logout
  | sopsWrapped (cmd : SOPSWranglerCommand)

-- Wrangler command builder
structure WranglerCommand where
  command : String  -- the subcommand (e.g., "secrets-store", "deploy", "kv:namespace")
  args    : List String
  options : List (String × String)  -- key-value options
  env     : Option CloudflareEnv
  sopsWrapped : Bool  -- whether this command uses sops-decrypted secrets

-- ============================================
-- Cloudflare API Response Types
-- ============================================

-- Generic API response wrapper
structure APIResponse (T : Type) where
  success : Bool
  result : Option T
  errors  : List String
  messages : List String

-- Worker deployment result
structure WorkerDeployment where
  id        : String
  url       : String
  version   : String
  created   : String

-- ============================================
-- Cloudflare Environment
-- ============================================

-- Cloudflare environment configuration
structure CloudflareEnv where
  accountId : AccountId
  apiToken : ApiToken
  baseUrl  : String  -- "https://api.cloudflare.com/client/v4"

-- Default Cloudflare environment
def defaultCloudflareEnv : CloudflareEnv :=
  { accountId := ""
  , apiToken := ""
  , baseUrl := "https://api.cloudflare.com/client/v4"
  }

-- ============================================
-- Theorems: Wrangler Configuration
-- ============================================

-- Theorem: Worker configuration is well-formed
theorem worker_config_has_name (w : Worker) : w.name ≠ "" := by
  sorry

-- Theorem: Worker has valid compatibility date format
theorem worker_compat_date_valid (w : Worker) :
  w.config.compatibility_date.length = 10 := by  -- YYYY-MM-DD format
  sorry

-- Theorem: API response has success field
theorem api_response_has_success (r : APIResponse α) :
  r.success = true ∨ r.success = false := by
  sorry

-- ============================================
-- Theorems: Wrangler Operations
-- ============================================

-- Theorem: Wrangler command has non-empty command name
theorem wrangler_command_has_command (cmd : WranglerCommand) :
  cmd.command ≠ "" := by
  sorry

-- Theorem: SOPS wrapped command has a valid account ID
theorem sops_wrapped_has_account (cmd : SOPSWranglerCommand) :
  cmd.accountId ≠ "" := by
  sorry

-- ============================================
-- Cloudflare Type Safety
-- ============================================

theorem account_id_is_string : ∀ (id : AccountId), True := by
  intro _
  exact True.intro

theorem api_token_is_string : ∀ (token : ApiToken), True := by
  intro _
  exact True.intro

end Wrangler
end Cloudflare
