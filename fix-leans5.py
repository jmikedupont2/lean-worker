p = "minimal/lean_worker_caller_combined.lean"
s = open(p).read()

# Fix the malformed end line
s = s.replace("end LeanWorkerCallerend LeanWorkerCaller\n", "end LeanWorkerCaller\n")

# Fix the caller_valid theorem (remove the wrong `exact` and the `unfold` chain)
old = """theorem leanWorker_caller_valid :
    verifiedCaller leanWorker_caller := by
  unfold verifiedCaller
  unfold gokujoCaller_isWellFormed
  constructor
  · simp [leanWorker_caller]
  · constructor
    · simp [gokujoCall_isParameterValid]
    · exact leanWorker_caller_valid"""

new = """theorem leanWorker_caller_valid :
    verifiedCaller leanWorker_caller := by
  unfold verifiedCaller
  unfold gokujoCaller_isWellFormed
  constructor
  · simp [leanWorker_caller]
  · constructor
    · simp [gokujoCall_isParameterValid]
    · constructor
      · rfl -- repoName ≠ ""
      · constructor
        · rfl -- gokujoCall_isParameterValid
        · unfold leanWorker_caller
          simp [gokujoCall_isParameterValid, verifiedRunner]
          constructor
          · rfl
          · constructor
            · intro r hr
              simp [leanWorker_caller.log] at hr
              rcases hr with (rfl | hr')
              · subst r
                constructor <;> rfl
              · constructor
                · rfl
                · dsimp; trivial"""

assert old in s, "caller block not found"
s = s.replace(old, new, 1)

open(p, "w").write(s)
print("patched")
