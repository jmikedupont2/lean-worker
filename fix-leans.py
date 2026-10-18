import re

p = "minimal/lean_worker_caller_combined.lean"
s = open(p).read()

# 1) Build caller valid: use simp only at top, then solve the list-membership with
#    rcases on the constructor, and decide the BuildKind match explicitly.
old = """theorem leanWorker_build_caller_valid : verifiedRunner leanWorker_build_caller.log := by
  constructor
  · exact leanWorker_build_caller_log_wellFormed
  · constructor
    · intro r hr
      simp only [verifiedRunner, leanWorker_build_caller] at hr
      rcases hr with (rfl | hr')
      · subst r
        exact exitCode_nonNeg r
      · cases hr'
    · intro r hr
      simp only [verifiedRunner, leanWorker_build_caller] at hr
      rcases hr with (rfl | hr')
      · subst r
        simp
      · cases hr'"""

new = """theorem leanWorker_build_caller_valid : verifiedRunner leanWorker_build_caller.log := by
  unfold verifiedRunner
  constructor
  · exact leanWorker_build_caller_log_wellFormed
  · intro r hr
    simp only [leanWorker_build_caller.log] at hr
    rcases hr with (rfl | hr')
    · subst r
      constructor
      · rfl
      · dsimp; trivial
    · constructor
      · rfl
      · dsimp; trivial"""

assert old in s, "build valid not found"
s = s.replace(old, new, 1)

# 2) Check caller valid: same fix
old2 = """theorem leanWorker_check_caller_valid : verifiedRunner leanWorker_check_caller.log := by
  constructor
  · exact leanWorker_check_caller_log_wellFormed
  · constructor
    · intro r hr
      simp only [verifiedRunner, leanWorker_check_caller] at hr
      rcases hr with (rfl | hr')
      · subst r
        exact exitCode_nonNeg r
      · cases hr'
    · intro r hr
      simp only [verifiedRunner, leanWorker_check_caller] at hr
      rcases hr with (rfl | hr')
      · subst r
        simp
      · cases hr'"""

new2 = """theorem leanWorker_check_caller_valid : verifiedRunner leanWorker_check_caller.log := by
  unfold verifiedRunner
  constructor
  · exact leanWorker_check_caller_log_wellFormed
  · intro r hr
    simp only [leanWorker_check_caller.log] at hr
    rcases hr with (rfl | hr')
    · subst r
      constructor
      · rfl
      · dsimp; trivial
    · constructor
      · rfl
      · dsimp; trivial"""

assert old2 in s, "check valid not found"
s = s.replace(old2, new2, 1)

open(p, "w").write(s)
print("patched")
