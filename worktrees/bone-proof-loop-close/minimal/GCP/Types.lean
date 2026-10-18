-- GCP Types
-- Formal model of Google Cloud Platform types
-- Aligned with the AWS model pattern (tools/gokujo/AWS/Types.lean)

namespace GCP

-- ============================================
-- Primitive Types
-- ============================================

-- GCP Project ID
abbrev ProjectId := String

-- GCP Region
abbrev Region := String

-- GCP Access Token
abbrev AccessToken := String

-- GCP API Key
abbrev APIKey := String

-- GCP Request ID
abbrev RequestId := String

-- ISO 8601 Timestamp
abbrev ISO8601Timestamp := String

-- Unix Timestamp
abbrev UnixTimestamp := Nat

-- ============================================
-- Build Types
-- ============================================

-- Build ID
def BuildId := String

-- Build Status
inductive BuildStatus
  | QUEUED
  | RUNNING
  | SUCCESS
  | FAILURE
  | TIMEOUT
  | CANCELLED

-- Build Trigger Template
structure BuildTriggerTemplate where
  triggerName : String
  pauseTime   : Nat
  retry       : Bool

-- Build Trigger
structure BuildTrigger where
  triggerId     : String
  triggerTemplate : BuildTriggerTemplate

-- ============================================
-- Artifact Registry Types
-- ============================================

-- Repository Name
abbrev RepositoryName := String

-- Repository ID
abbrev RepositoryId := String

-- Repository URI
abbrev RepositoryUri := String

-- Object Name
abbrev ObjectName := String

-- Bucket Name
abbrev BucketName := String

-- ============================================
-- Artifact Types
-- ============================================

-- Artifact ID
abbrev ArtifactId := String

-- Artifact Name
abbrev ArtifactName := String

-- Artifact URI
abbrev ArtifactUri := String

-- Artifact Type
abbrev ArtifactType := String

-- Artifact Metadata
structure ArtifactMetadata where
  name : String
  size : Nat
  checksum := String
