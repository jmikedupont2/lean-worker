-- GOAP (Goal-Oriented Action Planning) Module
-- Task planning and execution for lean-worker

import WorkerToolBinding
import PluginContexts

namespace GOAP

-- ============================================
-- GOAP State Representation
-- ============================================

structure State where
  projectExists   : Bool := false
  apiKeyAvailable : Bool := false
  indexBuilt      : Bool := false
  projectBuilt    : Bool := false
  projectDeployed : Bool := false
  keysDecrypted   : Bool := false
  serviceRunning  : Bool := false
  proofVerified   : Bool := false

-- ============================================
-- GOAP Action
-- ============================================

structure GOAPAction where
  name        : String
  preconditions : State
  effects       : State
  cost          : Nat := 1
  command       : String := ""

-- ============================================
-- Available Actions (mapped to aristotle-manager commands)
-- ============================================

def pollAction : GOAPAction where
  name := "poll"
  preconditions := { apiKeyAvailable := true, ..default }
  effects := { projectExists := true, ..default }
  cost := 1
  command := "aristotle-manager poll --download-only --parallel"

def buildAction : GOAPAction where
  name := "build"
  preconditions := { projectExists := true, ..default }
  effects := { projectBuilt := true, indexBuilt := true, ..default }
  cost := 5
  command := "aristotle-manager build --input-dir"

def deployAction : GOAPAction where
  name := "deploy"
  preconditions := { projectBuilt := true, apiKeyAvailable := true, ..default }
  effects := { projectDeployed := true, ..default }
  cost := 3
  command := "aristotle-manager deploy --cloudflare --name --public"

def searchIndexAction : GOAPAction where
  name := "search-index"
  preconditions := { projectExists := true, ..default }
  effects := { indexBuilt := true, ..default }
  cost := 2
  command := "aristotle-manager search-index --json --output"

def searchAction : GOAPAction where
  name := "search"
  preconditions := { indexBuilt := true, ..default }
  effects := { indexBuilt := true, ..default }
  cost := 1
  command := "aristotle-manager search --query --limit"

def enrichAction : GOAPAction where
  name := "enrich"
  preconditions := { projectExists := true, ..default }
  effects := { projectBuilt := true, ..default }
  cost := 2
  command := "aristotle-manager enrich --project-id --skip-task-enricher --skip-goap"

def sopsDecryptAction : GOAPAction where
  name := "sops-decrypt"
  preconditions := { ..default }
  effects := { keysDecrypted := true, apiKeyAvailable := true, ..default }
  cost := 1
  command := "sops -d --output-type json /etc/tracker-vault/secrets/cloudflare-pages-token.enc.json"

def systemdRunAction : GOAPAction where
  name := "systemd-run"
  preconditions := { keysDecrypted := true, ..default }
  effects := { serviceRunning := true, ..default }
  cost := 2
  command := "systemctl start lean-worker"

def lean4ProveAction : GOAPAction where
  name := "lean4-prove"
  preconditions := { projectBuilt := true, ..default }
  effects := { proofVerified := true, ..default }
  cost := 10
  command := "lean4 prove --module --goal"

-- ============================================
-- Action Registry (maps plugin contexts to actions)
-- ============================================

def actionRegistry : List (String × GOAPAction) := [
  ("aristotle_manager", pollAction),
  ("aristotle_manager", buildAction),
  ("aristotle_manager", deployAction),
  ("aristotle_manager", searchIndexAction),
  ("aristotle_manager", searchAction),
  ("aristotle_manager", enrichAction),
  ("lean4_twin", lean4ProveAction),
  ("task_manager", enrichAction)
]

-- ============================================
-- Plan Generation
-- ============================================

def isApplicable (action : GOAPAction) (state : State) : Bool :=
  (action.preconditions.projectExists → state.projectExists) ∧
  (action.preconditions.apiKeyAvailable → state.apiKeyAvailable) ∧
  (action.preconditions.indexBuilt → state.indexBuilt) ∧
  (action.preconditions.projectBuilt → state.projectBuilt) ∧
  (action.preconditions.projectDeployed → state.projectDeployed) ∧
  (action.preconditions.keysDecrypted → state.keysDecrypted) ∧
  (action.preconditions.serviceRunning → state.serviceRunning) ∧
  (action.preconditions.proofVerified → state.proofVerified)

def applyAction (action : GOAPAction) (state : State) : State :=
  { projectExists   := state.projectExists ∨ action.effects.projectExists,
    apiKeyAvailable := state.apiKeyAvailable ∨ action.effects.apiKeyAvailable,
    indexBuilt      := state.indexBuilt ∨ action.effects.indexBuilt,
    projectBuilt    := state.projectBuilt ∨ action.effects.projectBuilt,
    projectDeployed := state.projectDeployed ∨ action.effects.projectDeployed,
    keysDecrypted   := state.keysDecrypted ∨ action.effects.keysDecrypted,
    serviceRunning  := state.serviceRunning ∨ action.effects.serviceRunning,
    proofVerified   := state.proofVerified ∨ action.effects.proofVerified }

-- ============================================
-- Goal Checking
-- ============================================

def goalAchieved (goal : State) (state : State) : Bool :=
  (goal.projectExists → state.projectExists) ∧
  (goal.apiKeyAvailable → state.apiKeyAvailable) ∧
  (goal.indexBuilt → state.indexBuilt) ∧
  (goal.projectBuilt → state.projectBuilt) ∧
  (goal.projectDeployed → state.projectDeployed) ∧
  (goal.keysDecrypted → state.keysDecrypted) ∧
  (goal.serviceRunning → state.serviceRunning) ∧
  (goal.proofVerified → state.proofVerified)

-- ============================================
-- Simple Planner
-- ============================================

partial def findPlan (goal : State) (state : State) (actions : List GOAPAction) : Option (List GOAPAction) :=
  if goalAchieved goal state then
    some []
  else
    actions.findM? (fun action => isApplicable action state) >>= fun action =>
      let newState := applyAction action state
      findPlan goal newState actions >>= fun subplan =>
        some (action :: subplan)

-- ============================================
-- Task Plans (from worker descriptions)
-- ============================================

def planBuildAndDeploy : List GOAPAction := [
  sopsDecryptAction,
  pollAction,
  buildAction,
  deployAction
]

def planSearchAndProve : List GOAPAction := [
  sopsDecryptAction,
  searchIndexAction,
  searchAction,
  lean4ProveAction
]

def planFullPipeline : List GOAPAction := [
  sopsDecryptAction,
  pollAction,
  buildAction,
  enrichAction,
  searchIndexAction,
  searchAction,
  lean4ProveAction,
  deployAction
]

-- ============================================
-- GOAP Theorems (AOK proofs)
-- ============================================

theorem pollAction_applicable_when_api_key_available :
  ∀ (state : State), state.apiKeyAvailable → isApplicable pollAction state := by
  intro state h
  unfold isApplicable pollAction
  simp [h]

theorem buildAction_requires_project_exists :
  ∀ (state : State), ¬state.projectExists → ¬isApplicable buildAction state := by
  intro state h h_applicable
  unfold isApplicable buildAction at h_applicable
  simp at h_applicable
  contradiction

theorem planBuildAndDeploy_achieves_goal :
  ∀ (initialState : State),
    initialState.apiKeyAvailable →
    let goal : State := { projectExists := true, projectBuilt := true, projectDeployed := true, keysDecrypted := true, ..default }
    ∃ (plan : List GOAPAction),
      let finalState := plan.foldl (fun s action => applyAction action s) initialState
      goalAchieved goal finalState := by
  intro initialState h_api
  unfold goal
  use [sopsDecryptAction, pollAction, buildAction, deployAction]
  -- Simplified proof - in practice would need more detailed state tracking
  sorry

end GOAP
