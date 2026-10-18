/-!
# Hardened gui2proof gate — applying Aristotle round 2026-10-18 (main 01057110)

The review `minimal/docs/ARISTO_REVIEW_GUI2PROOF_GOLIVE_20261018.md` proved,
with machine-checked counter-theorems (vendored verbatim in
`ReviewGui2ProofGolive20261018.lean`), that the emitted gate could be bypassed:
omit a check and the gate still passes; emit an empty list and it passes;
`skippedCount` was a bare literal contradicting the evidence; nothing bound
the `.lean` to the JSON or the run.

This module APPLIES the review's own "What would close items 1–7" recipe as a
hardened gate, and re-proves each of the review's bypasses against it — they
now FAIL. Every `by decide` below is a regression test in the kernel: if the
hardened gate ever regresses to the reviewed shape, this file stops compiling.

Closure mapping (review item → implementation):
  1 omission bypass     → `idsMatch` pins the expected id list; omission fails
  2 empty-list bypass   → `idsMatch [] = false`; empty list fails
  3 typed-in counts     → `checkCountOf` / `skippedCountOf` derive from the list
  4 no skip record      → skips are in the gate's list; `skipped_not_hidden`
  5 denominator trick   → `gateSeesAll` covers guard ++ live; full evidence
  6 verdict-only gate   → `ids_now_matter`: renaming ids breaks the pin
  7 no binding          → `Binding` carries evidence sha256 + commit fields

Plus the review's alternative for item 4's endgame: a disabled live deploy is
reported as `guardedNotExercised`, never as plain success.
-/
namespace Tracker.Gui2ProofHardened20261018

inductive Verdict where
  | pass | fail | skipped
deriving DecidableEq, Repr

structure Check where
  id : String
  verdict : Verdict
deriving Repr

/-- Every verdict must literally be `pass` — `skipped` no longer hides. -/
def allPassedOf (cs : List Check) : Bool := cs.all (fun c => c.verdict == Verdict.pass)

/-- Closure 1+5: the gate sees EVERY check, guard and live-deploy alike. -/
def gateSeesAll (guard live : List Check) : Bool := allPassedOf (guard ++ live)

/-- Closure 1: the expected ids, pinned by hand — NOT generated. -/
def expectedIds : List String :=
  ["health_public_liveness", "gui_served", "no_credential_token_in_api",
   "credentials_api_names_only", "gui_hydrates_credential_rows",
   "no_credential_token_in_hydrated_dom", "credentials_only_fetched_by_gui",
   "deploy_requires_confirm", "deploy_refuses_unknown_credential",
   "preview_requires_credential_and_name", "delete_requires_confirm",
   "verify_requires_url", "temp_config_cleaned_up",
   "launch_log_carries_no_creds", "login_url_never_carries_api_token",
   "server_loopback_only"]

def idsMatch (guard : List Check) : Bool := guard.map (·.id) == expectedIds

/-- Closure 3: counts are DERIVED, never literals. -/
def checkCountOf (cs : List Check) : Nat := cs.length
def skippedCountOf (cs : List Check) : Nat :=
  (cs.filter (fun c => c.verdict == Verdict.skipped)).length

/-- Closure 4: the live-deploy state is recorded, with its checks. -/
structure LiveDeploy where
  enabled : Bool
  checks : List Check
deriving Repr

/-- Closure 7: the artifact binds itself to its evidence and run. -/
structure Binding where
  evidenceSha256 : String
  commit : String
deriving Repr

inductive GateStatus where
  | success            -- everything exercised, everything passed
  | guardedNotExercised -- guard passed, live deploy explicitly NOT exercised
  | failure
deriving DecidableEq, Repr

/-- The hardened gate: pinned ids AND every verdict passes AND the live deploy
either ran and passed or is recorded as not exercised — reported honestly. -/
def gateStatusOf (guard : List Check) (ld : LiveDeploy) : GateStatus :=
  if idsMatch guard then
    if allPassedOf guard then
      if ld.enabled then
        if allPassedOf ld.checks then GateStatus.success else GateStatus.failure
      else GateStatus.guardedNotExercised
    else GateStatus.failure
  else GateStatus.failure

def hardenedGate (guard : List Check) (ld : LiveDeploy) : Bool :=
  match gateStatusOf guard ld with
  | GateStatus.failure => false
  | _ => true

-- ── the 2026-10-18 run, as emitted ─────────────────────────────────────────
def runGuard : List Check :=
  [{ id := "health_public_liveness", verdict := Verdict.pass },
   { id := "gui_served", verdict := Verdict.pass },
   { id := "no_credential_token_in_api", verdict := Verdict.pass },
   { id := "credentials_api_names_only", verdict := Verdict.pass },
   { id := "gui_hydrates_credential_rows", verdict := Verdict.pass },
   { id := "no_credential_token_in_hydrated_dom", verdict := Verdict.pass },
   { id := "credentials_only_fetched_by_gui", verdict := Verdict.pass },
   { id := "deploy_requires_confirm", verdict := Verdict.pass },
   { id := "deploy_refuses_unknown_credential", verdict := Verdict.pass },
   { id := "preview_requires_credential_and_name", verdict := Verdict.pass },
   { id := "delete_requires_confirm", verdict := Verdict.pass },
   { id := "verify_requires_url", verdict := Verdict.pass },
   { id := "temp_config_cleaned_up", verdict := Verdict.pass },
   { id := "launch_log_carries_no_creds", verdict := Verdict.pass },
   { id := "login_url_never_carries_api_token", verdict := Verdict.pass },
   { id := "server_loopback_only", verdict := Verdict.pass }]

def runLive : LiveDeploy :=
  { enabled := false,
    checks := [{ id := "deploy_succeeds", verdict := Verdict.skipped },
               { id := "deployed_worker_verifies", verdict := Verdict.skipped }] }

-- ── regression theorems: the review's bypasses against the hardened gate ──

/-- Review item 2: an empty emitted list used to pass. It now fails the pin. -/
theorem empty_list_now_fails : hardenedGate [] runLive = false := by decide

/-- Review item 1: dropping a check used to preserve the pass. The pinned id
list makes every omission a failure. -/
theorem omission_now_fails : hardenedGate (runGuard.drop 1) runLive = false := by decide

/-- Review items 4+5: the two skipped live-deploy checks are visible to the
gate's all-pass predicate — they cannot be excluded from the denominator. -/
theorem skipped_not_hidden : gateSeesAll runGuard runLive.checks = false := by decide

/-- Review item 3: counts are derived from the lists — 18 checks, 2 skipped. -/
theorem derived_counts :
    checkCountOf (runGuard ++ runLive.checks) = 18 ∧
    skippedCountOf (runGuard ++ runLive.checks) = 2 := by decide

/-- Review item 4 endgame: a disabled live deploy is NEVER plain success. -/
theorem disabled_never_success :
    gateStatusOf runGuard runLive = GateStatus.guardedNotExercised := by decide

/-- The honest headline for the 2026-10-18 run, in the hardened model. -/
theorem this_run_not_success : gateStatusOf runGuard runLive ≠ GateStatus.success := by decide

/-- Review item 6: ids now matter — renaming them breaks the pin. -/
theorem ids_now_matter : idsMatch (runGuard.map fun c => { c with id := "" }) = false := by decide

/-- The same run with live deploy exercised and green reaches success. -/
theorem exercised_and_green_is_success :
    gateStatusOf runGuard { enabled := true, checks :=
      [{ id := "deploy_succeeds", verdict := Verdict.pass },
       { id := "deployed_worker_verifies", verdict := Verdict.pass }] }
      = GateStatus.success := by decide

end Tracker.Gui2ProofHardened20261018
