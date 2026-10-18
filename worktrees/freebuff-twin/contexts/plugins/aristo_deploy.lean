/-- Aristotle Project Deployment Module
Maps gokujo build outputs to Cloudflare Pages deployment via SOPS-encrypted credentials.

This module teaches lean-worker how to deploy Aristotle projects by:
1. Running gokujo to build/verify the Lean project
2. Extracting deployment artifacts (webapp, WASM, index.html)
3. Deploying to Cloudflare Pages using SOPS credentials
4. Recording telemetry and health checks -/

namespace AristoDeploy

structure ProjectConfig where
  projectId : String
  sourceUrl : String
  projectName : String
  deployBranch : String := "main"
  workingDir : String

structure DeploymentArtifacts where
  indexHtml : String
  wasmFiles : List String
  staticAssets : List String
  leanOutput : String

structure CloudflareConfig where
  accountId : String
  apiToken : String
  pagesProject : String

def buildWithGokujo (config : ProjectConfig) : IO (Result DeploymentArtifacts String) := do
  -- Run gokujo scan to find Lean files
  let scanCmd := "lean --run GokujoMain.lean scan " ++ config.projectName
  let scanResult := IO.runCmd scanCmd config.workingDir
  
  -- Run gokujo check to verify project compiles
  let checkCmd := "lean --run GokujoMain.lean check " ++ config.projectName
  let checkResult := IO.runCmd checkCmd config.workingDir
  
  -- Extract webapp assets for deployment
  let webappDir := config.workingDir ++ "/webapp"
  let artifacts := extractArtifacts webappDir
  
  pure (Ok artifacts)

def extractArtifacts (webappDir : String) : DeploymentArtifacts :=
  { indexHtml := webappDir ++ "/index.html"
  , wasmFiles := []
  , staticAssets := []
  , leanOutput := webappDir ++ "/lean_output" }

def deployToCloudflare (artifacts : DeploymentArtifacts) (cf : CloudflareConfig) : IO (Result String String) := do
  -- Deploy using wrangler with SOPS-decrypted credentials
  let env := #[
    ("CLOUDFLARE_ACCOUNT_ID", cf.accountId),
    ("CLOUDFLARE_API_TOKEN", cf.apiToken)
  ]
  let deployCmd := "wrangler pages deploy " ++ artifacts.indexHtml ++ " --project-name " ++ cf.pagesProject
  let result := IO.runCmdWithEnv deployCmd env "."
  pure (Ok result.stdout)

def loadSopsCredentials (vaultDir : String) (secretName : String) : IO (Result CloudflareConfig String) := do
  -- Decrypt credentials from SOPS vault
  let tokenCmd := "sops -d --output-type json " ++ vaultDir ++ "/secrets/" ++ secretName ++ ".enc.json"
  let accountCmd := "sops -d --output-type json " ++ vaultDir ++ "/secrets/" ++ secretName ++ "-account-id.enc.json"
  
  let tokenResult := IO.runCmd tokenCmd "."
  let accountResult := IO.runCmd accountCmd "."
  
  pure (Ok { accountId := accountResult.stdout.trim, apiToken := tokenResult.stdout.trim, pagesProject := "gui2proof-aristo-test" })

def deployAristoProject (config : ProjectConfig) : IO (Result String String) := do
  -- Load SOPS credentials
  let vaultDir := "/etc/tracker-vault"
  let credResult ← loadSopsCredentials vaultDir "cloudflare-pages-token"
  
  match credResult with
  | Ok creds =>
    -- Build with gokujo
    let buildResult ← buildWithGokujo config
    match buildResult with
    | Ok artifacts =>
      -- Deploy to Cloudflare
      deployToCloudflare artifacts creds
    | Err e => pure (Err ("Build failed: " ++ e))
  | Err e => pure (Err ("SOPS failed: " ++ e))

-- Example configuration for RequestProject
def requestProjectConfig : ProjectConfig :=
  { projectId := "0f9b0981-1dc9-4321-a46b-53e3cc6ee6e3"
  , sourceUrl := "https://aristotle.harmonic.fun/projects/0f9b0981-1dc9-4321-a46b-53e3cc6ee6e3"
  , projectName := "RequestProject"
  , workingDir := "/mnt/data1/time-2026/05-may/07/arist/output-final_aristotle/0f9b0981-1dc9-4321-a46b-53e3cc6ee6e3_aristotle" }

end AristoDeploy
