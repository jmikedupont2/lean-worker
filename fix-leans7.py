import re

p = "minimal/lean_worker_caller_combined.lean"
s = open(p).read()

# Find the marker we need to cut from. The clean split is:
# - Everything before `theorem callerRegistry_allWellFormed` belongs to the older proven part
# - After that we need a clean set of caller theorems + end block + combined example

marker = "theorem callerRegistry_allWellFormed :"
idx = s.find(marker)
assert idx != -1, "marker not found"

# Cut everything from marker onwards, but keep the `end LeanWorkerCaller` block's predecessor
# Actually, we want to keep the whole file up to `end LeanWorkerCaller` and then replace.

# Find the `end LeanWorkerCaller` that is currently at the head of the file (the one from line ~420)
# The first occurrence of `end LeanWorkerCaller` is the original end.
end_marker = "end LeanWorkerCaller"
end_idx = s.find(end_marker)

# Keep everything before `end LeanWorkerCaller`, discard the rest
head = s[:end_idx + len(end_marker)]

# Now build a clean tail
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
print("rewritten")
