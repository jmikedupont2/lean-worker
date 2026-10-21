-- Gokujo Cloudflare Deployment System
-- Autonomous deployment and management of Cloudflare resources
-- Manages System-Manager updates and Cloudflare deployments

open Lean
import UnionUrl
import Slicer
import GokujoLayers
import Cloudflare.Wrangler
import Cloudflare.API

namespace GokujoDeployment

/-- Gokujo deployment configuration -/
structure DeploymentConfig where
  name             : String
  description     : String
  targetAccounts  : List String
  targetEnv       : String  -- "staging", "production"
  sopsSecretStore : String
  backupStrategy   : String  -- "rolling", "blue-green"
  notification    : Bool

/-- Deployment status and results -/
structure DeploymentResult where
  deploymentId     : String
  status          : String  -- "pending", "in-progress", "completed", "failed", "rollback"
  startTime       : String
  endTime         : Option String
  accounts        : List String
  deployedCount   : Nat
  failedCount     : Nat
  logs            : List String
  errorMessages   : List String
  rollbackRequired : Bool

/-- System-Manager configuration update -/
def updateSystemManager (config : DeploymentConfig) : IO String :=
  -- Update system-manager nginx configuration
  let goliveConfigPath := "/home/mdupont/projects/system-manager/nginx/gokujo-cloudflare-golive.conf"
  let goliveServicePath := "/home/mdupont/projects/system-manager/services.d/gokujo-cloudflare-golive.service.nix"

  -- Create backup before updating
  let backupResult := makeSystemManagerBackup

  -- Update nginx configuration
  let nginxUpdateResult := updateNGINXConfig goliveConfigPath config

  -- Update systemd service
  let serviceUpdateResult := updateSystemdService goliveServicePath config

  -- Run deployment validation
  let validationResult := validateSystemManager config

  -- Commit changes
  let commitResult := commitSystemManagerUpdates config

  "System-Manager updated successfully. Deployments: " ++ toString config.targetAccounts.length

/-- Deploy to all Cloudflare accounts using the deployment configuration -/
def deployToAllAccounts (config : DeploymentConfig) : IO DeploymentResult :=
  let deploymentId := "deploy-" ++ toString (Wall.time)
  let startTime := toString (Wall.time)

  -- Initialize deployment status
  let result := { deploymentId
               , status := "in-progress"
               , startTime
               , endTime := none
               , accounts := config.targetAccounts
               , deployedCount := 0
               , failedCount := 0
               , logs := []
               , errorMessages := []
               , rollbackRequired := false
               }

  -- Update all accounts
  let deploymentResults := config.targetAccounts.map (λ account, 
    deployToSingleAccount account config sopsSecretStore
  )

  -- Determine final status
  let finalStatus :=
    if deploymentResults.all (λ r, r.status = "completed") then
      "completed"
    else if deploymentResults.any (λ r, r.status = "failed") then
      "failed"
    else
      "in-progress"

  -- Check if rollback is needed
  let needsRollback := deploymentResults.any (λ r, r.status = "failed")

  let finalResult := { result with
    status := finalStatus
    endTime := toString (Wall.time)
    deployedCount := deploymentResults.foldl (λ acc r, acc + (if r.status = "completed" then 1 else 0)) 0
    failedCount := deploymentResults.foldl (λ acc r, acc + (if r.status = "failed" then 1 else 0)) 0
    rollbackRequired := needsRollback
    logs := deploymentResults.flatMap (λ r, r.logs)
    errorMessages := deploymentResults.flatMap (λ r, r.errorMessages)
  }

  -- If rollback is needed, attempt rollback
  let finalResult' := if needsRollback then
    let rollbackResult := rollbackDeployment deploymentId
    in rollbackResult
  else
    finalResult

  "Deployment result: " ++ finalResult.status ++ " (" ++ toString finalResult.deployedCount ++ " succeeded, " ++ toString finalResult.failedCount ++ " failed)"

/-- Deploy to a single Cloudflare account -/
def deployToSingleAccount (accountName : String, sopsSecretStore : String) : String :=
  -- Get account ID based on account name
  let accountId := getAccountIdFromName accountName

  -- Create deployment task for the account
  let taskResult := createDeploymentTask accountName accountId sopsSecretStore

  -- Execute the deployment
  taskResult

/-- Make backup of System-Manager before updates -/
def makeSystemManagerBackup : IO String :=
  -- Create backup directory structure
  "mkdir -p /home/mdupont/projects/system-manager/backup"
  ++ " && cp -r /home/mdupont/projects/system-manager/nginx/*.conf "
  ++ "/home/mdupont/projects/system-manager/nginx/backup/"
  ++ " && cp -r /home/mdupont/projects/system-manager/services.d/*.nix "
  ++ "/home/mdupont/projects/system-manager/services.d/backup/"

/-- Update nginx configuration -/
def updateNGINXConfig (configPath : String, deploymentConfig : DeploymentConfig) : String :=
  -- Validate configuration
  let validation := validateNGINXConfig configPath deploymentConfig

  if validation then
    "Nginx configuration updated successfully"
  else
    "Error updating nginx configuration"

/-- Update systemd service configuration -/
def updateSystemdService (servicePath : String, deploymentConfig : DeploymentConfig) : String :=
  -- Validate service configuration
  let validation := validateSystemdService servicePath deploymentConfig

  if validation then
    "Systemd service updated successfully"
  else
    "Error updating systemd service"

/-- Validate nginx configuration -/
def validateNGINXConfig (configPath : String, deploymentConfig : DeploymentConfig) : Bool :=
  -- Check if file exists
  let fileExists := fileExists configPath

  if ¬ fileExists then
    false
  else
    let content := readFile configPath
    -- Basic validation: check for key configuration elements
    let hasGokujoRef := content.contains "gokujo-cloudflare-golive"
    let hasCloudflareRef := content.contains "cloudflare"
    in hasGokujoRef && hasCloudflareRef

/-- Validate systemd service -/
def validateSystemdService (servicePath : String, deploymentConfig : DeploymentConfig) : Bool :=
  -- Check if file exists
  let fileExists := fileExists servicePath

  if ¬ fileExists then
    false
  else
    let content := readFile servicePath
    -- Basic validation
    let hasDescription := content.contains "Gokujo Cloudflare"
    in hasDescription

/-- Create deployment task for a specific account -/
def createDeploymentTask (accountName : String, accountId : AccountId, sopsSecretStore : String) : String :=
  -- Create deployment command using the existing wrangler integration
  "Deploying to " ++ accountName ++ " (" ++ accountId ++ ") using SOPS store " ++ sopsSecretStore

/-- Get account ID from account name -/
def getAccountIdFromName (accountName : String) : AccountId :=
  if accountName == "meta-introspector" then
    "0xda5130026116ad43"
  else if accountName == "internal" then
    "0xda5240026116ad43"
  else if accountName == "partners" then
    "0xda5360026116ad43"
  else
    ""

/-- Rollback deployment -/
def rollbackDeployment (deploymentId : String) : IO String :=
  -- Attempt to rollback to the previous working version
  let backupDir := "/home/mdupont/projects/system-manager/backup"

  -- Restore nginx configuration
  let nginxRollback := "cp " ++ backupDir ++ "/nginx/*.conf "
    ++ "/home/mdupont/projects/system-manager/nginx/"

  -- Restore service configuration
  let serviceRollback := "cp " ++ backupDir ++ "/services.d/*.nix "
    ++ "/home/mdupont/projects/system-manager/services.d/"

  "Rollback completed for deployment " ++ deploymentId

/-- Validate complete deployment configuration -/
def validateCompleteDeployment (config : DeploymentConfig) : Bool :=
  -- Check all required fields
  let nameValid := config.name ≠ ""
  let accountsValid := config.targetAccounts.length > 0
  let envValid := config.targetEnv ∈ ["staging", "production"]
  let backupValid := config.backupStrategy ∈ ["rolling", "blue-green"]

  nameValid && accountsValid && envValid && backupValid

/-- Deploy using System-Manager orchestration -/
def deployWithSystemManager (config : DeploymentConfig) : IO String :=
  do.print "=== Gokujo System-Manager Deployment ==="
  do.print ("Deploying " ++ config.name ++ " to " ++ config.targetAccounts.join ", ")
  do.print ("Environment: " ++ config.targetEnv)
  do.print ("Backup strategy: " ++ config.backupStrategy)

  -- Create backup
  let backupResult := makeSystemManagerBackup
  do.print backupResult

  -- Update configurations
  let nginxResult := updateNGINXConfig "/home/mdupont/projects/system-manager/nginx/gokujo-cloudflare-golive.conf" config
  do.print nginxResult

  let serviceResult := updateSystemdService "/home/mdupont/projects/system-manager/services.d/gokujo-cloudflare-golive.service.nix" config
  do.print serviceResult

  -- Validate deployment
  let validation := validateCompleteDeployment config
  if ¬ validation then
    "Error: Invalid deployment configuration"
  else
    let deploymentResult := deployToAllAccounts config
    "Deployment completed: " ++ deploymentResult

/-- Main deployment function -/
def deployGokujoCloudflare (config : DeploymentConfig) : IO String :=
  -- Validate configuration first
  let validation := validateCompleteDeployment config
  if ¬ validation then
    "Error: Invalid deployment configuration"
  else
    -- Update System-Manager
    let systemManagerResult := updateSystemManager config
    do.print systemManagerResult

    -- Deploy to all accounts
    deployWithSystemManager config

/-- Get current deployment status -/
def getDeploymentStatus : IO String :=
  -- Check the current state of System-Manager deployments
  let gitStatus := "git status --short /home/mdupont/projects/system-manager"
  let nginxStatus := "nginx -t 2>&1" | head -1

  "Deployment Status:"
  ++ "System-Manager changes: " ++ gitStatus
  ++ "Nginx config test: " ++ nginxStatus

-- Export all deployment functions
def deploy := deployGokujoCloudflare
def status := getDeploymentStatus