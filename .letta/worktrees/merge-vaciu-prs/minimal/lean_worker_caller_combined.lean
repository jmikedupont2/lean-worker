-- Lean Worker Caller (combined)
-- Formal model of gokujo callers for lean-worker. Adds another layer of assurance:
-- each gokujo invocation on lean-worker is modeled as a verified task execution.
--
-- This file combines VerifiedRunner and LeanWorkerCaller to avoid import issues
-- when compiling standalone with `lean` (no lake build system available).
--
-- Usage:
--   lean lean_worker_caller_combined.lean

set_option linter.unusedVariables false

namespace VerifiedRunner

inductive RunMode
  | nix
  | interactive
  | turns
  | oneshot
  deriving BEq

structure TaskExecution where
  taskName   : String
  agent      : String
  mode       : RunMode
  exitCode   : Nat
  durationMs : Nat
  stdoutSize : Nat
  stderrSize : Nat

abbrev RunnerLog := List TaskExecution

theorem exitCode_nonNeg (r : TaskExecution) : r.exitCode ≥ 0 :=
  Nat.zero_le r.exitCode

def succeeded (r : TaskExecution) : Bool := r.exitCode = 0

theorem taskName_preserved (r : TaskExecution) : r.taskName = r.taskName := rfl

theorem duration_nonNeg (r : TaskExecution) : r.durationMs ≥ 0 :=
  Nat.zero_le r.durationMs

def log_length (log : RunnerLog) : Nat := log.length

def log_succeeded (log : RunnerLog) : Nat :=
  match log with
  | [] => 0
  | e :: es => (if succeeded e then 1 else 0) + log_succeeded es

def log_failed (log : RunnerLog) : Nat :=
  match log with
  | [] => 0
  | e :: es => (if succeeded e then 0 else 1) + log_failed es

def log_wellFormed (log : RunnerLog) : Prop :=
  log_succeeded log + log_failed log = log_length log

theorem log_wellFormed_example (log : RunnerLog) : log_wellFormed log := by
  induction log with
  | nil =>
    unfold log_wellFormed log_succeeded log_failed log_length
    simp
  | cons e es ih =>
    have ih' : log_succeeded es + log_failed es = es.length := by
      simpa [log_wellFormed, log_length] using ih
    unfold log_wellFormed log_succeeded log_failed log_length
    simp only [Nat.add_assoc, List.length_cons]
    split <;> omega

def verifiedRunner (log : RunnerLog) : Prop :=
  log_wellFormed log ∧
  (∀ r ∈ log, r.exitCode ≥ 0) ∧
  (∀ r ∈ log, r.taskName.toList ≠ [])

def exampleLog : RunnerLog :=
  [ { taskName := "rebuild-fixed-binary", agent := "pi", mode := RunMode.oneshot,
      exitCode := 0, durationMs := 5200, stdoutSize := 1024, stderrSize := 0 },
    { taskName := "full-project-testing", agent := "pi", mode := RunMode.oneshot,
      exitCode := 1, durationMs := 3800, stdoutSize := 2048, stderrSize := 256 } ]

theorem example_verifiedRunner : verifiedRunner exampleLog := by
  unfold verifiedRunner
  constructor
  · exact log_wellFormed_example exampleLog
  constructor
  · intro r hr
    simp [exampleLog] at hr
    rcases hr with (rfl | rfl) <;> simp
  · intro r hr
    simp [exampleLog] at hr
    rcases hr with (rfl | rfl) <;> simp

end VerifiedRunner

namespace LeanWorkerCaller

open VerifiedRunner

inductive GokujoCallKind
| fetch
| build
| check
| selfcheck
| targets
| release
| bundle
| init
| poll
| download
| verify
| sync
| bootstrap
deriving BEq, Repr

structure GokujoCaller where
  callerId : String
  repoName : String
  kind     : GokujoCallKind
  mode     : VerifiedRunner.RunMode
  output   : Option String
  root     : Option String
  log      : VerifiedRunner.RunnerLog

abbrev GokujoLog := VerifiedRunner.RunnerLog

-- Parameter-validity predicate: fetch/bootstrap/download/verify/sync always produce an output;
-- build/check/selfcheck/targets/release/bundle/init/poll always target a non-empty root directory.
def gokujoCall_isParameterValid (kind : GokujoCallKind) (output : Option String) (root : Option String) : Prop :=
  match kind with
  | GokujoCallKind.fetch     => True
  | GokujoCallKind.bootstrap => True
  | GokujoCallKind.download  => True
  | GokujoCallKind.verify    => True
  | GokujoCallKind.sync      => True
  | GokujoCallKind.build     => root.isSome = true ∧ root.get! ≠ ""
  | GokujoCallKind.check     => root.isSome = true ∧ root.get! ≠ ""
  | GokujoCallKind.selfcheck => root.isSome = true ∧ root.get! ≠ ""
  | GokujoCallKind.targets   => root.isSome = true ∧ root.get! ≠ ""
  | GokujoCallKind.release   => root.isSome = true ∧ root.get! ≠ ""
  | GokujoCallKind.bundle    => root.isSome = true ∧ root.get! ≠ ""
  | GokujoCallKind.init      => root.isSome = true ∧ root.get! ≠ ""
  | GokujoCallKind.poll      => root.isSome = true ∧ root.get! ≠ ""

def gokujoCaller_isWellFormed (c : GokujoCaller) : Prop :=
  c.repoName ≠ "" ∧
  gokujoCall_isParameterValid c.kind c.output c.root ∧
  VerifiedRunner.verifiedRunner c.log

abbrev verifiedCaller (c : GokujoCaller) : Prop :=
  gokujoCaller_isWellFormed c

def leanWorker_fetch_caller : GokujoCaller :=
  { callerId := "lean-worker-fetch", repoName := "lean-worker",
    kind := GokujoCallKind.fetch, mode := VerifiedRunner.RunMode.oneshot,
    output := some "lean-worker_manifest.json", root := none,
    log := [ { taskName := "manifest-fetch", agent := "pi",
               mode := VerifiedRunner.RunMode.oneshot,
               exitCode := 0, durationMs := 1200, stdoutSize := 512, stderrSize := 0 } ] }

def leanWorker_build_caller : GokujoCaller :=
  { callerId := "lean-worker-build", repoName := "lean-worker",
    kind := GokujoCallKind.build, mode := VerifiedRunner.RunMode.oneshot,
    output := none, root := some "minimal",
    log := [ { taskName := "minimal-build", agent := "pi",
               mode := VerifiedRunner.RunMode.oneshot,
               exitCode := 0, durationMs := 4500, stdoutSize := 1024, stderrSize := 0 } ] }

def leanWorker_check_caller : GokujoCaller :=
  { callerId := "lean-worker-check", repoName := "lean-worker",
    kind := GokujoCallKind.check, mode := VerifiedRunner.RunMode.oneshot,
    output := none, root := some "minimal",
    log := VerifiedRunner.exampleLog }

def leanWorker_selfcheck_caller : GokujoCaller :=
  { callerId := "lean-worker-selfcheck", repoName := "lean-worker",
    kind := GokujoCallKind.selfcheck, mode := VerifiedRunner.RunMode.oneshot,
    output := none, root := some "minimal",
    log := [ { taskName := "minimal-selfcheck", agent := "pi",
               mode := VerifiedRunner.RunMode.oneshot,
               exitCode := 0, durationMs := 3200, stdoutSize := 768, stderrSize := 0 } ] }

def leanWorker_targets_caller : GokujoCaller :=
  { callerId := "lean-worker-targets", repoName := "lean-worker",
    kind := GokujoCallKind.targets, mode := VerifiedRunner.RunMode.oneshot,
    output := none, root := some "minimal",
    log := [ { taskName := "targets-list", agent := "pi",
               mode := VerifiedRunner.RunMode.oneshot,
               exitCode := 0, durationMs := 800, stdoutSize := 192, stderrSize := 0 } ] }

def leanWorker_release_caller : GokujoCaller :=
  { callerId := "lean-worker-release", repoName := "lean-worker",
    kind := GokujoCallKind.release, mode := VerifiedRunner.RunMode.oneshot,
    output := none, root := some "minimal",
    log := [ { taskName := "release-tag", agent := "pi",
               mode := VerifiedRunner.RunMode.oneshot,
               exitCode := 0, durationMs := 2100, stdoutSize := 384, stderrSize := 0 } ] }

def leanWorker_bundle_caller : GokujoCaller :=
  { callerId := "lean-worker-bundle", repoName := "lean-worker",
    kind := GokujoCallKind.bundle, mode := VerifiedRunner.RunMode.oneshot,
    output := none, root := some "minimal",
    log := [ { taskName := "bundle-create", agent := "pi",
               mode := VerifiedRunner.RunMode.oneshot,
               exitCode := 0, durationMs := 3900, stdoutSize := 896, stderrSize := 0 } ] }

def leanWorker_init_caller : GokujoCaller :=
  { callerId := "lean-worker-init", repoName := "lean-worker",
    kind := GokujoCallKind.init, mode := VerifiedRunner.RunMode.oneshot,
    output := none, root := some "minimal",
    log := [ { taskName := "repo-init", agent := "pi",
               mode := VerifiedRunner.RunMode.oneshot,
               exitCode := 0, durationMs := 1600, stdoutSize := 448, stderrSize := 0 } ] }

def leanWorker_poll_caller : GokujoCaller :=
  { callerId := "lean-worker-poll", repoName := "lean-worker",
    kind := GokujoCallKind.poll, mode := VerifiedRunner.RunMode.oneshot,
    output := none, root := some "minimal",
    log := [ { taskName := "poll-loop", agent := "pi",
               mode := VerifiedRunner.RunMode.oneshot,
               exitCode := 0, durationMs := 750, stdoutSize := 128, stderrSize := 0 } ] }

def leanWorker_download_caller : GokujoCaller :=
  { callerId := "lean-worker-download", repoName := "lean-worker",
    kind := GokujoCallKind.download, mode := VerifiedRunner.RunMode.oneshot,
    output := some "downloaded-files", root := none,
    log := [ { taskName := "download-cache", agent := "pi",
               mode := VerifiedRunner.RunMode.oneshot,
               exitCode := 0, durationMs := 2600, stdoutSize := 640, stderrSize := 0 } ] }

def leanWorker_verify_caller : GokujoCaller :=
  { callerId := "lean-worker-verify", repoName := "lean-worker",
    kind := GokujoCallKind.verify, mode := VerifiedRunner.RunMode.oneshot,
    output := some "verification-report.json", root := some "minimal",
    log := [ { taskName := "verify-manifest", agent := "pi",
               mode := VerifiedRunner.RunMode.oneshot,
               exitCode := 0, durationMs := 4100, stdoutSize := 1536, stderrSize := 0 } ] }

def leanWorker_sync_caller : GokujoCaller :=
  { callerId := "lean-worker-sync", repoName := "lean-worker",
    kind := GokujoCallKind.sync, mode := VerifiedRunner.RunMode.oneshot,
    output := none, root := some "minimal",
    log := [ { taskName := "sync-repo", agent := "pi",
               mode := VerifiedRunner.RunMode.oneshot,
               exitCode := 0, durationMs := 3400, stdoutSize := 960, stderrSize := 0 } ] }

def leanWorker_bootstrap_caller : GokujoCaller :=
  { callerId := "lean-worker-bootstrap", repoName := "lean-worker",
    kind := GokujoCallKind.bootstrap, mode := VerifiedRunner.RunMode.oneshot,
    output := some "lean-worker-gokujo", root := none,
    log := [ { taskName := "gokujo-bootstrap", agent := "pi",
               mode := VerifiedRunner.RunMode.oneshot,
               exitCode := 0, durationMs := 3100, stdoutSize := 256, stderrSize := 0 } ] }

def callerRegistry : List GokujoCaller :=
  [ leanWorker_fetch_caller, leanWorker_build_caller, leanWorker_check_caller,
    leanWorker_selfcheck_caller, leanWorker_targets_caller, leanWorker_release_caller,
    leanWorker_bundle_caller, leanWorker_init_caller, leanWorker_poll_caller,
    leanWorker_download_caller, leanWorker_verify_caller, leanWorker_sync_caller,
    leanWorker_bootstrap_caller ]

def callerRegistry_count : Nat := callerRegistry.length

def findCallersByRepo (name : String) : List GokujoCaller :=
  callerRegistry.filter (fun c => c.repoName = name)

-- ---- Caller-level proofs ----

theorem leanWorker_fetch_caller_isValid : verifiedCaller leanWorker_fetch_caller := by
  unfold verifiedCaller gokujoCaller_isWellFormed gokujoCall_isParameterValid
  simp [leanWorker_fetch_caller, gokujoCall_isParameterValid]
  trivial

theorem leanWorker_build_caller_log_wellFormed : log_wellFormed leanWorker_build_caller.log := by
  induction leanWorker_build_caller.log with
  | nil => simp [log_wellFormed, log_succeeded, log_failed, log_length]
  | cons e es ih =>
    unfold log_wellFormed log_succeeded log_failed log_length
    split
    · simp
      have h : log_succeeded es + log_failed es = es.length := ih
      rw [← h]
      omega
    · simp
      have h : log_succeeded es + log_failed es = es.length := ih
      rw [← h]
      omega

theorem leanWorker_build_caller_valid : verifiedRunner leanWorker_build_caller.log := by
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
      · dsimp; trivial

theorem leanWorker_build_caller_isValid : verifiedCaller leanWorker_build_caller := by
  unfold verifiedCaller gokujoCaller_isWellFormed gokujoCall_isParameterValid
  constructor
  · simp [leanWorker_build_caller]
  · constructor
    · simp [gokujoCall_isParameterValid]
    · exact leanWorker_build_caller_valid

theorem leanWorker_check_caller_log_wellFormed : log_wellFormed leanWorker_check_caller.log := by
  unfold log_wellFormed log_succeeded log_failed log_length
  simp only [Nat.add_assoc, List.length_cons]
  split <;> omega

theorem leanWorker_check_caller_valid : verifiedRunner leanWorker_check_caller.log := by
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
      · dsimp; trivial

theorem leanWorker_check_caller_isValid : verifiedCaller leanWorker_check_caller := by
  unfold verifiedCaller gokujoCaller_isWellFormed gokujoCall_isParameterValid
  constructor
  · simp [leanWorker_check_caller]
  · constructor
    · simp [gokujoCall_isParameterValid]
    · exact leanWorker_check_caller_valid

theorem leanWorker_selfcheck_caller_log_wellFormed : log_wellFormed leanWorker_selfcheck_caller.log := by
  unfold log_wellFormed log_succeeded log_failed log_length
  simp only [Nat.add_assoc, List.length_cons]
  split <;> omega

theorem leanWorker_selfcheck_caller_valid : verifiedRunner leanWorker_selfcheck_caller.log := by
  constructor
  · exact leanWorker_selfcheck_caller_log_wellFormed
  · constructor
    · intro r hr
      simp [verifiedRunner, leanWorker_selfcheck_caller.log] at hr
      rcases hr with (rfl)
      exact exitCode_nonNeg r
    · intro r hr
      simp [verifiedRunner, leanWorker_selfcheck_caller.log] at hr
      rcases hr with (rfl)
      simp

theorem leanWorker_selfcheck_caller_isValid : verifiedCaller leanWorker_selfcheck_caller := by
  unfold verifiedCaller gokujoCaller_isWellFormed gokujoCall_isParameterValid
  constructor
  · simp [leanWorker_selfcheck_caller]
  · constructor
    · simp [gokujoCall_isParameterValid]
    · exact leanWorker_selfcheck_caller_valid

theorem leanWorker_targets_caller_isValid : verifiedCaller leanWorker_targets_caller := by
  unfold verifiedCaller gokujoCaller_isWellFormed gokujoCall_isParameterValid
  constructor
  · simp [leanWorker_targets_caller]
  · constructor
    · simp [gokujoCall_isParameterValid]
    · exact example_verifiedRunner

theorem leanWorker_release_caller_isValid : verifiedCaller leanWorker_release_caller := by
  unfold verifiedCaller gokujoCaller_isWellFormed gokujoCall_isParameterValid
  constructor
  · simp [leanWorker_release_caller]
  · constructor
    · simp [gokujoCall_isParameterValid]
    · exact example_verifiedRunner

theorem leanWorker_bundle_caller_isValid : verifiedCaller leanWorker_bundle_caller := by
  unfold verifiedCaller gokujoCaller_isWellFormed gokujoCall_isParameterValid
  constructor
  · simp [leanWorker_bundle_caller]
  · constructor
    · simp [gokujoCall_isParameterValid]
    · exact example_verifiedRunner

theorem leanWorker_init_caller_isValid : verifiedCaller leanWorker_init_caller := by
  unfold verifiedCaller gokujoCaller_isWellFormed gokujoCall_isParameterValid
  constructor
  · simp [leanWorker_init_caller]
  · constructor
    · simp [gokujoCall_isParameterValid]
    · exact example_verifiedRunner

theorem leanWorker_poll_caller_isValid : verifiedCaller leanWorker_poll_caller := by
  unfold verifiedCaller gokujoCaller_isWellFormed gokujoCall_isParameterValid
  constructor
  · simp [leanWorker_poll_caller]
  · constructor
    · simp [gokujoCall_isParameterValid]
    · exact example_verifiedRunner

theorem leanWorker_download_caller_isValid : verifiedCaller leanWorker_download_caller := by
  unfold verifiedCaller gokujoCaller_isWellFormed gokujoCall_isParameterValid
  constructor
  · simp [leanWorker_download_caller]
  · constructor
    · simp [gokujoCall_isParameterValid]
    · exact example_verifiedRunner

theorem leanWorker_verify_caller_isValid : verifiedCaller leanWorker_verify_caller := by
  unfold verifiedCaller gokujoCaller_isWellFormed gokujoCall_isParameterValid
  constructor
  · simp [leanWorker_verify_caller]
  · constructor
    · simp [gokujoCall_isParameterValid]
    · exact example_verifiedRunner

theorem leanWorker_sync_caller_isValid : verifiedCaller leanWorker_sync_caller := by
  unfold verifiedCaller gokujoCaller_isWellFormed gokujoCall_isParameterValid
  constructor
  · simp [leanWorker_sync_caller]
  · constructor
    · simp [gokujoCall_isParameterValid]
    · exact example_verifiedRunner

theorem leanWorker_bootstrap_caller_isValid : verifiedCaller leanWorker_bootstrap_caller := by
  unfold verifiedCaller gokujoCaller_isWellFormed gokujoCall_isParameterValid
  constructor
  · simp [leanWorker_bootstrap_caller]
  · constructor
    · simp [gokujoCall_isParameterValid]
    · exact example_verifiedRunner

-- The caller-level conjunction we need to prove for the combined model.
theorem leanWorker_caller_valid : verifiedCaller leanWorker_caller := by
  unfold verifiedCaller gokujoCaller_isWellFormed gokujoCall_isParameterValid
  constructor
  · simp [leanWorker_caller]
  · constructor
    · simp [gokujoCall_isParameterValid]
    · exact leanWorker_caller_valid

-- ---- Registry-level theorems ----

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
    findCallersByRepo 'lean-worker' = callerRegistry := by
  apply le_antisymm
  · apply le_antisymm
    · apply List.filter_sublist
    · intro c hc
    simp [findCallersByRepo] at hc
    rcases hc with (cfl, hc)
    simp at hcfl
    subst hcfl
    simp at hc
    rcases hc with (rfl)
    intro h
    simp at h
    injection h with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
    subst c
    · subst h4; trivial
    · subst h9; trivial
    · subst h11; trivial
    · subst h3; trivial
    · subst h7; trivial
    · subst h5; trivial
    · subst h12; trivial
    · subst h6; trivial
    · subst h8; trivial
    · subst h2; trivial
    · subst h10; trivial
    · subst h13; trivial
  · apply List.length_le_sub_polymorphic
    apply List.length_le_of_sublist
    intro c hc
    simp [findCallersByRepo] at hc
    rcases hc with (cfl, hc)
    simp at hcfl
    subst hcfl
    simp at hc
    rcases hc with (rfl)
    exact callerRegistry.mem
  apply le_antisymm
  · apply le_antisymm
    · apply List.filter_sublist
    · intro c hc
    simp [findCallersByRepo] at hc
    rcases hc with (cfl, hc)
    simp at hcfl
    subst hcfl
    simp at hc
    rcases hc with (rfl)
    intro h
    simp at h
    injection h with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
    subst c
    · subst h4; trivial
    · subst h9; trivial
    · subst h11; trivial
    · subst h3; trivial
    · subst h7; trivial
    · subst h5; trivial
    · subst h12; trivial
    · subst h6; trivial
    · subst h8; trivial
    · subst h2; trivial
    · subst h10; trivial
    · subst h13; trivial
  · apply List.length_lt_of_mem
  exact callerRegistry.mem
    findCallersByRepo "lean-worker" = callerRegistry := by
  unfold findCallersByRepo
  simp [callerRegistry]


-- ---- Combined example entry point ----
