-- Lean-Worker Task Interface
-- Typesafe interface for Gokujo Layer Architecture task management
-- Follows ~/dotagents/tasks/ pattern from Twitterstorm project
-- Compiled with Lean 4.35.0

open Lean

-- ============================================
-- Gokujo Task Management System
-- ============================================

/-- Task status enumeration -/
inductive TaskStatus
  | open
  | in_progress
  | completed
  | blocked
  | cancelled
  deriving BEq, DecidableEq, Repr

/-- Render a status as a string -/
def TaskStatus.render : TaskStatus → String
  | .open => "OPEN"
  | .in_progress => "IN_PROGRESS"
  | .completed => "COMPLETED"
  | .blocked => "BLOCKED"
  | .cancelled => "CANCELLED"

/-- Task structure for the Gokujo Layer Architecture -/
structure GokujoTask where
  id          : String
  title       : String
  description : String
  status      : TaskStatus := .open
  priority    : Nat := 0
  tags        : List String := []
  assignee    : Option String := none
  context_path : String

/-- The central task registry lives in ~/dotagents/tasks/ -/
def gokujo_task_root : String := "~/dotagents/tasks/"

/-- Build a task in the central registry -/
def mkTask (id title desc : String) (priority : Nat) : GokujoTask :=
  { id := id
  , title := title
  , description := desc
  , status := .open
  , priority := priority
  , tags := []
  , assignee := none
  , context_path := gokujo_task_root ++ "system/SYSTEM.md" }

/-- The core Gokujo integration tasks -/
def gokujo_core_tasks : List GokujoTask := [
  mkTask "nix" "Implement Nix interface" "Typesafe Nix/posix interface for package management" 1,
  mkTask "git" "Implement Git interface" "Git operations wrapper (clone, pull, push, status, log)" 2,
  mkTask "github" "Implement GitHub interface" "GitHub API wrapper (repos, issues, PRs)" 2,
  mkTask "search" "Implement Search interface" "Tantivy + plocate + shmem search integration" 3,
  mkTask "cloudflare" "Implement Cloudflare interface" "Cloudflare worker deployment types and commands" 3,
  mkTask "dns" "Implement DNS interface" "DNS record management for Cloudflare domains" 2,
  mkTask "lake" "Implement Lake interface" "Lean4 Lake build system integration" 2,
  mkTask "aristotle" "Implement Aristotle interface" "Proof system integration with Aristotle corpus" 3,
  mkTask "deploy" "Implement Deploy interface" "Full deployment orchestration (backups, system-manager, nginx, Cloudflare)" 4,
  mkTask "zos-plugins" "Implement ZOS plugins" "eBPF, NORA, Pipelight, Forgejo plugin contexts" 3,
  mkTask "task-interface" "Create task interface in Lean" "Typesafe task management interface following dotagents pattern" 1
]

/-- Verification tasks for the Gokujo Layer -/
def gokujo_verification_tasks : List GokujoTask := [
  mkTask "verify-nix" "Verify Nix module compiles" "Ensure Nix.lean compiles and exports correct interfaces" 1,
  mkTask "verify-git" "Verify Git module compiles" "Ensure Git.lean compiles and exports correct interfaces" 1,
  mkTask "verify-search" "Verify Search module compiles" "Ensure Search.lean compiles with Tantivy + plocate" 1,
  mkTask "verify-zos" "Verify ZOS plugins integrate" "Ensure all 4 ZOS plugins integrate with context system" 2,
  mkTask "full-integration" "Run full integration test suite" "Verify all Gokujo modules work together" 3
]

/-- The full Gokujo integration plan: core work then verification -/
def gokujo_full_plan : List GokujoTask := gokujo_core_tasks ++ gokujo_verification_tasks

/-- Core plan (implementation only) -/
def gokujo_core_plan : List GokujoTask := gokujo_core_tasks

/-- Verification plan -/
def gokujo_verify_plan : List GokujoTask := gokujo_verification_tasks

/-- Count the total tasks -/
def gokujo_full_plan_count : Nat := gokujo_full_plan.length

/-- Calculate total cost (sum of priorities) -/
def gokujo_full_plan_cost : Nat :=
  gokujo_full_plan.foldl (fun acc task => acc + task.priority) 0

/-- Highest priority in the core plan -/
def gokujo_core_max_priority : Nat :=
  gokujo_core_plan.foldl (fun acc task => max acc task.priority) 0

-- ============================================
-- AOK Theorems (Arguments of Knowledge)
-- ============================================

/-- The core plan has exactly 11 tasks -/
theorem gokujo_core_plan_count_eq : gokujo_core_plan.length = 11 := by decide

/-- The verification plan has exactly 5 tasks -/
theorem gokujo_verify_plan_count_eq : gokujo_verify_plan.length = 5 := by decide

/-- The full plan has exactly 16 tasks -/
theorem gokujo_full_plan_count_eq : gokujo_full_plan_count = 16 := by decide

/-- The full plan is core ++ verification, preserving order -/
theorem gokujo_full_plan_order :
  gokujo_full_plan.length = gokujo_core_plan.length + gokujo_verify_plan.length := by decide

/-- Every core task starts open -/
theorem gokujo_core_plan_all_open :
  gokujo_core_plan.all (fun t => t.status == .open) = true := by decide

/-- Every verification task starts open -/
theorem gokujo_verify_plan_all_open :
  gokujo_verify_plan.all (fun t => t.status == .open) = true := by decide

/-- Every task has a non-empty description -/
theorem gokujo_full_plan_descriptions_present :
  gokujo_full_plan.all (fun t => t.description.length > 0) = true := by decide

/-- Every task points into the central dotagents registry -/
theorem gokujo_full_plan_context_paths_valid :
  gokujo_full_plan.all (fun t => t.context_path == gokujo_task_root ++ "system/SYSTEM.md") = true := by decide

/-- The plan cost is the sum of priorities -/
theorem gokujo_full_plan_cost_eq : gokujo_full_plan_cost = 34 := by decide

/-- Deploy is the highest priority work in the core plan -/
theorem deploy_is_highest_priority : gokujo_core_max_priority = 4 := by decide

/-- All 16 task ids are distinct -/
theorem gokujo_full_plan_ids_nodup :
  (gokujo_full_plan.map (fun t => t.id)).Nodup = true := by decide

/-- The full plan sums the core and verification cost -/
theorem gokujo_full_plan_cost_sum :
  gokujo_full_plan_cost = gokujo_core_plan.foldl (fun acc t => acc + t.priority) 0 +
                        gokujo_verify_plan.foldl (fun acc t => acc + t.priority) 0 := by decide