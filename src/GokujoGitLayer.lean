-- Gokujo Git Layer Module
-- Integrates git path management with the Gokujo Layer Architecture
-- Hosted at: https://github.com/meta-introspector/llama.cpp.git

open Lean
import UnionUrl
import Slicer
import GokujoLayers

namespace GokujoGitLayer

/-- Canonical git SCM URL for the Llama.cpp repository -/
def canonicalGitUrl : String :=
  "https://github.com/meta-introspector/llama.cpp.git"

/-- Read relative paths from the Aristotle git repository -/
-- Path: /mnt/data1/all_aristo_git.txt
def readAristoPaths : List String :=

let gitFilePath : String := "/mnt/data1/all_aristo_git.txt"

if hasFile gitFilePath then
  let content : String := getFileContents gitFilePath
  content.split("\n").filter (λ line, line ≠ "") else
    List.nil

/-- Extract lean file paths from the git entries -/
def extractLeanPaths (paths : List String) : List String :=
  paths.filter (λ path, path.endsWith ".lean")

/-- Display git layer status -/
def displayGitLayerStatus : IO Unit :=
  do.print "=== Gokujo Git Layer Status ==="
  do.print ("Canonical URL: " ++ canonicalGitUrl)
  do.print ("Plugin host path: " ++ "lean-worker/gokujo-git-layer")
  do.print ("Lean paths found: " ++ extractLeanPaths (readAristoPaths).length)
  do.print ("All paths count: " ++ readAristoPaths.length)
  do.print ""
  do.print "Lean paths:"
  LeanPaths.iter (λ path, do.print ("  - " ++ path))

-- Export the lean paths for use by other modules
def leanPaths : List String =
  extractLeanPaths (readAristoPaths)

-- Debug output
#eval displayGitLayerStatus
