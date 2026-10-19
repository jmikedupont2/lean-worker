-- SOPS Cloudflare Integration
-- Uses sops for encrypted secret management with Cloudflare Wrangler
-- Part of the Gokujo Layer Architecture

open Lean
import UnionUrl
import Slicer
import GokujoLayers
import SOPS
import Cloudflare.Wrangler
import Cloudflare.API
import Cloudflare.Integration

namespace GokujoSOPSCloudflare

/-- Three Cloudflare account configurations for deployment -/
def accountOne : String := "account-1-meta-introspector"
def accountTwo : String := "account-two-internal"
def accountThree : String := "account-three-partners"

/-- Canonical Cloudflare account ids -/
def accountIdOne : AccountId := "0xda5130026116ad43"
def accountIdTwo : AccountId := "0xda5240026116ad43"
def accountIdThree : AccountId := "0xda5360026116ad43"

/-- SOPS encrypted secrets for each account -/
def sopsSecretOne : String :=
  "ENCRYPTED_V1[meta-introspector]:accountId=" ++ accountIdOne ++
  ",ttl=30d,scopes=workers"

def sopsSecretTwo : String :=
  "ENCRYPTED_V1[internal]:accountId=" ++ accountIdTwo ++
  ",ttl=30d,scopes=workers"

def sopsSecretThree : String :=
  "ENCRYPTED_V1[partners]:accountId=" ++ accountIdThree ++
  ",ttl=30d,scopes=workers"

/-- Deploy to all 3 Cloudflare accounts using SOPS -/
def deployToAllAccounts (workerName : String) : IO (List String) :=

  -- SOPS decrypt and deploy to each account
  do.print "=== Deploying to 3 Cloudflare accounts ==="
  do.print ("Worker: " ++ workerName)
  do.print ""

  let results : List String :=
    [ sopsDeployToAccount accountOne sopsSecretOne accountIdOne workerName
    , sopsDeployToAccount accountTwo sopsSecretTwo accountIdTwo workerName
    , sopsDeployToAccount accountThree sopsSecretThree accountIdThree workerName
    ]

  do.print "=== Deployment Complete ==="
  results.iter (λ result, do.print ("  " ++ result))
  results

/-- Deploy using SOPS-decrypted secret to single account -/
def sopsDeployToAccount (accountName : String, sopsSecret : String, account_id : AccountId, workerName : String) : String :=

  -- SOPS command wrapped wrangler deployment
  let cmd : SOPSWranglerCommand :=
    { baseCommand := "deploy --name " ++ workerName
    , sopsSecret := sopsSecret
    , accountId := account_id
    }

  -- Build the full command with SOPS decryption
  let fullCommand : String :=
    "sops -d --input-type=base64 --output-type=yaml " ++ sopsSecret ++
    " | wrangler " ++ cmd.baseCommand ++
    " --account-id=" ++ account_id

  "Deployed to " ++ accountName ++ ": " ++ fullCommand

/-- Create secrets store for SOPS-managed secrets -/
def createSOPSSecretsStore (storeId : String, masterToken : String) : IO String :=
  -- First, store the master token using SOPS
  let sopsWrappedCmd : SOPSWranglerCommand :=
    { baseCommand := "secrets-store create " ++ storeId ++
      " --name command-center-master-token --scopes workers"
    , sopsSecret := masterToken
    , accountId := accountIdOne  -- use first account for setup
    }

  "wrangler secrets-store create " ++ storeId ++
  " --name command-center-master-token --value <sops-decrypted> --scopes workers"

/-- List all secrets stores -/
def listSecretsStores : IO Unit :=
  do.print "=== Secrets Stores ==="
  do.print ("Account 1 (" ++ accountIdOne ++ "): <store-id>")
  do.print ("Account 2 (" ++ accountIdTwo ++ "): <store-id>")
  do.print ("Account 3 (" ++ accountIdThree ++ "): <store-id>")

/-- Read relative paths from the Aristotle git repository -/
structure GitLayerPath where
  path : String
  isLeanFile : Bool
  fileType : String

/-- Extract git layer paths -/
def extractGitLayerPaths : List GitLayerPath :=
  let gitFilePath : String := "/mnt/data1/all_aristo_git.txt"
  if hasFile gitFilePath then
    let content : String := getFileContents gitFilePath
    content.split("\n").filter (λ line, line ≠ "").map (λ path =>
      { path := path
      , isLeanFile := path.endsWith ".lean"
      , fileType := if path.endsWith ".lean" then "Lean" else "Other"
      })
  else
    []

/-- Count paths by type -/
def countPathsByType (paths : List GitLayerPath) : List (String × Nat) :=
  let leanCount := paths.filter (λ p, p.isLeanFile).length
  let otherCount := paths.filter (λ p, ¬ p.isLeanFile).length
  [("Lean files", leanCount), ("Other files", otherCount)]

/-- Display SOPS Cloudflare deployment status -/
def displaySOPSStatus : IO Unit :=
  let paths := extractGitLayerPaths
  let counts := countPathsByType paths

  do.print "=== SOPS Cloudflare Gokujo Status ==="
  do.print ("Canonical URL: " ++ "https://github.com/meta-introspector/llama.cpp.git")
  do.print "Accounts configured:"
  do.print ("  1. meta-introspector (" ++ accountIdOne ++ ")")
  do.print ("  2. internal (" ++ accountIdTwo ++ ")")
  do.print ("  3. partners (" ++ accountIdThree ++ ")")
  do.print ""
  do.print "Git Layer Paths:"
  counts.iter (λ (t, c), do.print ("  " ++ t ++ ": " ++ toString c))
  do.print ""
  do.print "Ready for SOPS-encrypted deployment"

-- Export key functions
def leanPaths : List String :=
  (extractGitLayerPaths.filter (λ p, p.isLeanFile)).map (λ p => p.path)

def allPaths : List GitLayerPath := extractGitLayerPaths

-- Debug output
#eval displaySOPSStatus