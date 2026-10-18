p = "minimal/lean_worker_caller_combined.lean"
s = open(p).read()

# Find the end of the original file content: the first `end LeanWorkerCaller` at line 420ish.
# Then rebuild the tail.
lines = s.split("\n")

# Find the line index of the first `end LeanWorkerCaller` (the one that ends the namespace)
end_idx = None
for i, ln in enumerate(lines):
    if ln.strip() == "end LeanWorkerCaller":
        end_idx = i
        break
assert end_idx is not None, "no end block"

head = "\n".join(lines[:end_idx + 1])

new_tail = """-- ---- Caller-level theorems ----

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

theorem callerRegistry_has_verified_callers :
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

open(p, "w").write(head + new_tail)
print("rewritten, lines:", len((head + new_tail).split("\n")))
