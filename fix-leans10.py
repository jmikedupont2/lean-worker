p = "minimal/lean_worker_caller_combined.lean"
s = open(p).read()

old = """theorem find_lean_worker_callers :
    findCallersByRepo "lean-worker" = callerRegistry := by
  simp [findCallersByRepo, callerRegistry]"""

new = """theorem find_lean_worker_callers :
    findCallersByRepo "lean-worker" = callerRegistry := by
  unfold findCallersByRepo
  simp [callerRegistry]"""

assert old in s
s = s.replace(old, new, 1)

open(p, "w").write(s)
print("done")
