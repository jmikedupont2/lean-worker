/-!
# Review of `Gui2ProofGolive.lean` (gui2proof go-live round, 2026-10-18)

The definitions `Verdict`, `Check`, `allPassedOf` reproduce the emitted
artifact's model verbatim (with `allPassed` generalised to an arbitrary check
list), so the facts below are facts about the artifact's own gate.

`emitted` is the 16-entry list in the artifact; `evidenceAll` is every check
recorded in `gui2proof-golive.json` (16 guard + 2 live-deploy).
-/

namespace Tracker.Review.Gui2ProofGolive20261018

inductive Verdict where
  | pass | fail | skipped
deriving DecidableEq, Repr

structure Check where
  id : String
  verdict : Verdict
deriving Repr

/-- The artifact's `allPassed`, as a function of the emitted list. -/
def allPassedOf (cs : List Check) : Bool := cs.all (fun c => c.verdict == Verdict.pass)

/-- The 16 checks emitted into the artifact. -/
def emitted : List Check :=
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

/-- The two live-deploy checks recorded as skipped in the evidence. -/
def liveDeploy : List Check :=
  [{ id := "deploy_succeeds", verdict := Verdict.skipped },
   { id := "deployed_worker_verifies", verdict := Verdict.skipped }]

/-- Every check recorded in the evidence file. -/
def evidenceAll : List Check := emitted ++ liveDeploy

/-- The artifact's headline theorem holds for the emitted list (sanity check). -/
theorem emitted_allPassed : allPassedOf emitted = true := by decide

/-- An EMPTY emitted list also satisfies the gate: the theorem
`allPassed = true` compiles even if the generator emits no checks at all. -/
theorem empty_list_passes_gate : allPassedOf [] = true := rfl

/-- Dropping ANY subset of checks preserves a passing gate; in particular a
generator that omits a failed check (instead of emitting `Verdict.fail`)
still yields a compiling artifact. -/
theorem omitting_checks_preserves_pass (cs ds : List Check)
    (h : allPassedOf (cs ++ ds) = true) : allPassedOf cs = true := by
  unfold allPassedOf at *
  rw [List.all_append] at h
  exact (Bool.and_eq_true _ _ ▸ h).1

/-- A failing check can be erased from the record and the gate passes. -/
theorem failed_check_erased_still_passes :
    allPassedOf (emitted ++ [{ id := "deploy_requires_confirm", verdict := Verdict.fail }])
      = false ∧ allPassedOf emitted = true := by decide

/-- Over the FULL evidence (18 checks), the artifact's own predicate is false:
the run's `16/16` headline is obtained only by excluding the two skipped
checks from the list the gate sees. -/
theorem full_evidence_fails_gate : allPassedOf evidenceAll = false := by decide

/-- The evidence records 18 checks, 2 of them skipped. -/
theorem evidence_counts :
    evidenceAll.length = 18 ∧
    (evidenceAll.filter (fun c => c.verdict == Verdict.skipped)).length = 2 ∧
    (evidenceAll.filter (fun c => c.verdict == Verdict.pass)).length = 16 := by decide

/-- The artifact's `skippedCount := 0` disagrees with the evidence's 2 skipped
checks; it is a bare literal, not derived from any list. -/
theorem artifact_skippedCount_contradicts_evidence :
    (evidenceAll.filter (fun c => c.verdict == Verdict.skipped)).length ≠ 0 := by decide

/-- `allPassedOf` ignores everything except the verdict tag: two lists with
the same verdicts and arbitrary ids (e.g. all empty strings) are
indistinguishable to the gate. The artifact carries no evidence strings, so
the theorem cannot depend on any concrete evidence. -/
theorem gate_ignores_ids (cs : List Check) :
    allPassedOf (cs.map fun c => { c with id := "" }) = allPassedOf cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [allPassedOf, List.all_cons] at *; rw [ih]

end Tracker.Review.Gui2ProofGolive20261018
