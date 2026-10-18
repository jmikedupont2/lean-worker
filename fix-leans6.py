p = "minimal/lean_worker_caller_combined.lean"
s = open(p).read()

# The file currently ends with the broken `callerRegistry_count` / `find_lean_worker_callers` region
# mixed with the new caller-level theorems. Replace everything after
# `theorem callerRegistry_has_verified_callers : ...` plus body with a clean tail.

marker = """theorem callerRegistry_has_verified_callers :
    callerRegistry_count > 0 ∧ ∃ c ∈ callerRegistry, verifiedCaller c := by
  constructor
  · unfold callerRegistry_count callerRegistry
    simp [List.length]
  · use leanWorker_fetch_caller
    simp [callerRegistry]
    exact leanWorker_fetch_caller_isValid
"""

idx = s.find(marker)
assert idx != -1, "marker not found"

clean_tail = marker + """

theorem callerRegistry_allWellFormed :
    ∀ c ∈ callerRegistry, verifiedCaller c := by
  intro c hc
  simp [callerRegistry] at hc
  subst hc
  all_goals
    unfold verifiedCaller gokujoCaller_isWellFormed gokujoCall_isParameterValid
    constructor
    · assumption
    · constructor
      · assumption
      · assumption

theorem callerRegistry_has_verified_callers_gen :
    callerRegistry_count > 0 ∧ ∃ c ∈ callerRegistry, verifiedCaller c := by
  constructor
  · unfold callerRegistry_count callerRegistry
    simp [List.length]
  · use leanWorker_fetch_caller
    simp [callerRegistry]
    exact leanWorker_fetch_caller_isValid

theorem find_lean_worker_callers :
    findCallersByRepo "lean-worker" = callerRegistry := by
  simp [findCallersByRepo, callerRegistry]

theorem find_unknown_callers :
    findCallersByRepo "nonexistent" = [] := by
  simp [findCallersByRepo, callerRegistry]

end LeanWorkerCaller

-- ---- Combined example entry point ----

/-- The full verified lean-worker caller model for standalone `lean` compilation. -/
def leanWorker_allVerified : Prop :=
  VerifiedRunner.verifiedRunner leanWorker_caller.log ∧
  VerifiedRunner.verifiedRunner leanWorker_fetch_caller.log ∧
  VerifiedRunner.verifiedRunner leanWorker_build_caller.log ∧
  VerifiedRunner.verifiedRunner leanWorker_check_caller.log ∧
  VerifiedRunner.verifiedRunner leanWorker_selfcheck_caller.log ∧
  VerifiedRunner.verifiedRunner leanWorker_targets_caller.log ∧
  VerifiedRunner.verifiedRunner leanWorker_release_caller.log ∧
  VerifiedRunner.verifiedRunner leanWorker_bundle_caller.log ∧
  VerifiedRunner.verifiedRunner leanWorker_init_caller.log ∧
  VerifiedRunner.verifiedRunner leanWorker_poll_caller.log ∧
  VerifiedRunner.verifiedRunner leanWorker_download_caller.log ∧
  VerifiedRunner.verifiedRunner leanWorker_verify_caller.log ∧
  VerifiedRunner.verifiedRunner leanWorker_sync_caller.log ∧
  VerifiedRunner.verifiedRunner leanWorker_bootstrap_caller.log
"""

open(p, "w").write(s[:idx] + clean_tail)
print("rewritten")
