import re

p = "minimal/lean_worker_caller_combined.lean"
s = open(p).read()

# Replace the callerRegistry_allWellFormed theorem
old = """theorem callerRegistry_allWellFormed :
    ∀ c ∈ callerRegistry, verifiedCaller c := by
  intro c hc
  simp [callerRegistry] at hc
  subst hc
  <;> assumption"""

new = """theorem callerRegistry_allWellFormed :
    ∀ c ∈ callerRegistry, verifiedCaller c := by
  intro c hc
  simp [callerRegistry] at hc
  subst hc
  · exact leanWorker_fetch_caller_isValid
  · exact leanWorker_build_caller_isValid
  · exact leanWorker_check_caller_isValid
  · exact leanWorker_selfcheck_caller_isValid
  · exact leanWorker_targets_caller_isValid
  · exact leanWorker_release_caller_isValid
  · exact leanWorker_bundle_caller_isValid
  · exact leanWorker_init_caller_isValid
  · exact leanWorker_poll_caller_isValid
  · exact leanWorker_download_caller_isValid
  · exact leanWorker_verify_caller_isValid
  · exact leanWorker_sync_caller_isValid
  · exact leanWorker_bootstrap_caller_isValid"""

assert old in s, "reg found"
s = s.replace(old, new, 1)

# Replace the callerRegistry_has_verified_callers theorem
old2 = """theorem callerRegistry_has_verified_callers :
    callerRegistry_count > 0 ∧ ∃ c ∈ callerRegistry, verifiedCaller c := by
  constructor
  · unfold callerRegistry_count callerRegistry
    simp [List.length]
  · use leanWorker_fetch_caller
    simp [callerRegistry]
    exact leanWorker_fetch_caller_isValid"""

new2 = """theorem callerRegistry_has_verified_callers :
    callerRegistry_count > 0 ∧ ∃ c ∈ callerRegistry, verifiedCaller c := by
  constructor
  · unfold callerRegistry_count callerRegistry
    simp [List.length]
  · use leanWorker_fetch_caller
    simp [callerRegistry]
    exact leanWorker_fetch_caller_isValid"""

assert old2 in s, "reg2 found"
s = s.replace(old2, new2, 1)

# --- Fix the main callerValid theorem ---
old_main = """theorem leanWorker_caller_valid :
    verifiedCaller leanWorker_caller := by
  unfold verifiedCaller gokujoCaller_isWellFormed gokujoCall_isParameterValid
  constructor
  · simp [leanWorker_caller]
  · constructor
    · simp [gokujoCall_isParameterValid]
    · exact leanWorker_caller_valid"""

new_main = """theorem leanWorker_caller_valid :
    verifiedCaller leanWorker_caller := by
  unfold verifiedCaller gokujoCaller_isWellFormed gokujoCall_isParameterValid
  constructor
  · simp [leanWorker_caller]
  · constructor
    · simp [gokujoCall_isParameterValid]
    · exact leanWorker_caller_valid"""

assert old_main in s, "main found"
s = s.replace(old_main, new_main, 1)

# fix: verifiedCaller c now unfolds to gokujoCaller_isWellFormed c, which is a conjunction.
# We need to destruct it manually.
old_wrap = """theorem callerRegistry_allWellFormed :
    ∀ c ∈ callerRegistry, verifiedCaller c := by
  intro c hc
  simp [callerRegistry] at hc
  subst hc
  · exact leanWorker_fetch_caller_isValid
  · exact leanWorker_build_caller_isValid
  · exact leanWorker_check_caller_isValid
  · exact leanWorker_selfcheck_caller_isValid
  · exact leanWorker_targets_caller_isValid
  · exact leanWorker_release_caller_isValid
  · exact leanWorker_bundle_caller_isValid
  · exact leanWorker_init_caller_isValid
  · exact leanWorker_poll_caller_isValid
  · exact leanWorker_download_caller_isValid
  · exact leanWorker_verify_caller_isValid
  · exact leanWorker_sync_caller_isValid
  · exact leanWorker_bootstrap_caller_isValid"""

new_wrap = """theorem callerRegistry_allWellFormed :
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
      · exact <assumption>"""

# Actually, the structure is:
# verifiedCaller c = gokujoCaller_isWellFormed c (a Prop)
# gokujoCaller_isWellFormed c = c.repoName ≠ "" ∧ gokujoCall_isParameterValid ... ∧ verifiedRunner c.log
# So after unfold, we need to prove a 3-conjunction.
# But actually `verifiedCaller` is an abbrev for `gokujoCaller_isWellFormed c`.
# So `unfold verifiedCaller` turns `verifiedCaller c` into `gokujoCaller_isWellFormed c`.
# Then we can `unfold gokujoCaller_isWellFormed` to get the conjunction.
# Let me rewrite the whole theorem.

old_wrap2 = """theorem callerRegistry_allWellFormed :
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
      · exact <assumption>"""

new_wrap2 = """theorem callerRegistry_allWellFormed :
    ∀ c ∈ callerRegistry, verifiedCaller c := by
  intro c hc
  simp [callerRegistry] at hc
  subst hc
  all_goals
    unfold verifiedCaller
    -- verifiedCaller c = gokujoCaller_isWellFormed c
    unfold gokujoCaller_isWellFormed
    -- now target: c.repoName ≠ "" ∧ gokujoCall_isParameterValid c.kind c.output c.root ∧ verifiedRunner c.log
    constructor
    · assumption
    · constructor
      · assumption
      · assumption"""

assert old_wrap2 in s, "wrap2 found"
s = s.replace(old_wrap2, new_wrap2, 1)

# Fix leanWorker_caller_valid
old_caller = """theorem leanWorker_caller_valid :
    verifiedCaller leanWorker_caller := by
  unfold verifiedCaller gokujoCaller_isWellFormed gokujoCall_isParameterValid
  constructor
  · simp [leanWorker_caller]
  · constructor
    · simp [gokujoCall_isParameterValid]
    · exact leanWorker_caller_valid"""

new_caller = """theorem leanWorker_caller_valid :
    verifiedCaller leanWorker_caller := by
  unfold verifiedCaller
  unfold gokujoCaller_isWellFormed
  constructor
  · simp [leanWorker_caller]
  · constructor
    · simp [gokujoCall_isParameterValid]
    · exact leanWorker_caller_valid"""

assert old_caller in s, "caller not found"
s = s.replace(old_caller, new_caller, 1)

open(p, "w").write(s)
print("patched")
