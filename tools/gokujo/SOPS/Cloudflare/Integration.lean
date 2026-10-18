-- SOPS Cloudflare Integration
-- Uses sops for encrypted secret management with Cloudflare Wrangler

open Lean
import UnionUrl
import Slicer
import GokujoLayers
import SOPS

namespace GokujoSOPSCloudflare

/-- Three Cloudflare account configurations for deployment -/
def accountOne : String := "account-1-meta-introspector"
def accountTwo : String := "account-two-internal"
def accountThree : String := "account-three-partners"

/-- Canonical Cloudflare account IDs -/
def accountIdOne : String := "0xda5130026116ad43"
def accountIdTwo : String := "0xda5240026116ad43"
def accountIdThree : String := "0xda5360026116ad43"

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
    [ deployToAccount accountOne sopsSecretOne
    , deployToAccount accountTwo sopsSecretTwo
    , deployToAccount accountThree sopsSecretThree
    ]
  
  do.print "=== Deployment Complete ==="
  results.iter (λ result, do.print ("  " ++ result))
  results

/-- Deploy SOPS-encrypted secret to single account -/
def deployToAccount (accountName : String, sopsSecret : String) : String :=

  -- Use sops to decrypt and wrangler to deploy
  let decryptedSecret : String :=
    sops "decrypt" ++ " --input-type=" ++
    "base64" ++ " --output-type=" ++ "yaml" ++
    " " ++ sopsSecret
  
  let deploymentResult : String :=
    "wrangler publish" ++
    " --account=" ++ accountName ++
    " --secret=" ++ decryptedSecret ++
    " --name=" ++ workerName
  
  "Deployed to " ++ accountName ++ ": " ++ deploymentResult

/-- Initialize SOPS secret store for Cloudflare -/
def initSOPSCloudflareStore : IO Unit :=
  do.print "=== Initializing SOPS Cloudflare Secret Store ==="
  do.print ("Account 1: " ++ accountOne ++ " (" ++ accountIdOne ++ ")")
  do.print ("Account 2: " ++ accountTwo ++ " (" ++ accountIdTwo ++ ")")
  do.print ("Account 3: " ++ accountThree ++ " (" ++ accountIdThree ++ ")")
  do.print ""
  do.print "Secrets will be stored encrypted with sops"
  do.print "Use: sops --encrypt --input-type=yaml --output-type=sops <secret-file>"
  do.print ""
  do.print "After initial setup, master token can be revoked"
  do.print "Subsequent deployments use scoped worker tokens only"

-- Debug output
#eval deployToAllAccounts "my-gokujo-worker"