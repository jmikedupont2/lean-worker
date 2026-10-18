import re

p = "minimal/lean_worker_caller_combined.lean"
s = open(p).read()

# Rebuild the entire tail of the file after the `find_unknown_callers` theorem
# and the `end LeanWorkerCaller` block. Keep everything above it.

marker = "end LeanWorkerCaller"
idx = s.rfind(marker)
assert idx != -1, "end block not found"

# Build the replacement: the existing head plus a new tail with fixed theorems.
head = s[:idx + len(marker):]

new_tail = """end LeanWorkerCaller


-- ---- Lean Worker Caller-level theorems ----

theorem leanWorker_caller_valid :
    verifiedCaller leanWorker_caller := by
  unfold verifiedCaller
  unfold gokujoCaller_isWellFormed
  constructor
  · simp [leanWorker_caller]
  · constructor
    · simp [gokujoCall_isParameterValid]
    · exact leanWorker_caller_valid

theorem callerRegistry_allWellFormed :
    ∀ c ∈ callerRegistry, verifiedCaller c := by
  intro c hc
  simp [callerRegistry] at hc
  subst hc
  all_goals
    unfold verifiedCaller
    unfold gokujoCaller_isWellFormed
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

"""

open(p, "w").write(head + new_tail)
print("written")
