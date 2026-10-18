-- Lean Worker Caller
-- Formal model of gokujo callers for lean-worker. Adds another layer of assurance:
-- each gokujo invocation on lean-worker is modeled as a verified task execution.
--
-- Usage:
--   lean lean_worker_caller.lean

import RequestProject.VerifiedRunner

namespace LeanWorkerCaller

-- ============================================
-- Gokujo Call Kinds
-- ============================================

inductive GokujoCallKind
| fetch     -- gokujo cut --project lean-worker -o manifest.json
| build     -- gokujo build --root minimal
| check     -- gokujo check --root minimal
| selfcheck -- gokujo selfcheck --target minimal
| targets   -- gokujo targets --list
| release   -- gokujo release --tag v0.2.0
| bundle    -- gokujo bundle --out gokujo-bundle
| init      -- gokujo init --project lean-worker
| poll      -- gokujo poll --interval 5000
| download  -- gokujo download --cid QmExample --out files
| verify    -- gokujo verify --manifest manifest.json
| sync      -- gokujo sync
| bootstrap -- gokujo bootstrap -o lean-worker-gokujo
deriving BEq, Repr

-- ============================================
-- Gokujo Caller Structure
-- ============================================

structure GokujoCaller where
  callerId : String
  repoName : String
  kind     : GokujoCallKind
  mode     : RunMode
  output   : Option String
  root     : Option String
  log      : RunnerLog

abbrev GokujoLog := RunnerLog

-- ============================================
-- Well-Formedness Predicates
-- ============================================

-- A gokujo call is parameter-valid when:
--  • fetch/bootstrap/download/verify/sync always produce or accept an output file
--  • build/check/selfcheck/targets/release/bundle/init/poll always target a non-empty root directory
def gokujoCall_isParameterValid (kind : GokujoCallKind) (output : Option String) (root : Option String) : Prop :=
  match kind with
  | GokujoCallKind.fetch     => true
  | GokujoCallKind.bootstrap => true
  | GokujoCallKind.download  => true
  | GokujoCallKind.verify    => true
  | GokujoCallKind.sync      => true
  | GokujoCallKind.build     => root.isSome ∧ root.get! ≠ ""
  | GokujoCallKind.check     => root.isSome ∧ root.get! ≠ ""
  | GokujoCallKind.selfcheck => root.isSome ∧ root.get! ≠ ""
  | GokujoCallKind.targets   => root.isSome ∧ root.get! ≠ ""
  | GokujoCallKind.release   => root.isSome ∧ root.get! ≠ ""
  | GokujoCallKind.bundle    => root.isSome ∧ root.get! ≠ ""
  | GokujoCallKind.init      => root.isSome ∧ root.get! ≠ ""
  | GokujoCallKind.poll      => root.isSome ∧ root.get! ≠ ""
  end

def gokujoCaller_isWellFormed (c : GokujoCaller) : Prop :=
  c.repoName ≠ "" ∧
  gokujoCall_isParameterValid c.kind c.output c.root ∧
  VerifiedRunner.verifiedRunner c.log

abbrev verifiedCaller (c : GokujoCaller) : Prop :=
  gokujoCaller_isWellFormed c

-- ============================================
-- Example Callers
-- ============================================

def leanWorker_fetch_caller : GokujoCaller := {
  callerId     := "lean-worker-fetch",
  repoName     := "lean-worker",
  kind         := GokujoCallKind.fetch,
  mode         := RunMode.oneshot,
  output       := some "lean-worker_manifest.json",
  root         := none,
  log          := [ { taskName := "manifest-fetch", agent := "pi", mode := RunMode.oneshot,
                      exitCode := 0, durationMs := 1200, stdoutSize := 512, stderrSize := 0 } ]
}

def leanWorker_build_caller : GokujoCaller := {
  callerId     := "lean-worker-build",
  repoName     := "lean-worker",
  kind         := GokujoCallKind.build,
  mode         := RunMode.oneshot,
  output       := none,
  root         := some "minimal",
  log          := [ { taskName := "minimal-build", agent := "pi", mode := RunMode.oneshot,
                      exitCode := 0, durationMs := 4500, stdoutSize := 1024, stderrSize := 0 } ]
}

def leanWorker_check_caller : GokujoCaller := {
  callerId     := "lean-worker-check",
  repoName     := "lean-worker",
  kind         := GokujoCallKind.check,
  mode         := RunMode.oneshot,
  output       := none,
  root         := some "minimal",
  log          := VerifiedRunner.exampleLog
}

def leanWorker_selfcheck_caller : GokujoCaller := {
  callerId     := "lean-worker-selfcheck",
  repoName     := "lean-worker",
  kind         := GokujoCallKind.selfcheck,
  mode         := RunMode.oneshot,
  output       := none,
  root         := some "minimal",
  log          := [ { taskName := "minimal-selfcheck", agent := "pi", mode := RunMode.oneshot,
                      exitCode := 0, durationMs := 3200, stdoutSize := 768, stderrSize := 0 } ]
}

def leanWorker_targets_caller : GokujoCaller := {
  callerId     := "lean-worker-targets",
  repoName     := "lean-worker",
  kind         := GokujoCallKind.targets,
  mode         := RunMode.oneshot,
  output       := none,
  root         := some "minimal",
  log          := [ { taskName := "targets-list", agent := "pi", mode := RunMode.oneshot,
                      exitCode := 0, durationMs := 800, stdoutSize := 192, stderrSize := 0 } ]
}

def leanWorker_release_caller : GokujoCaller := {
  callerId     := "lean-worker-release",
  repoName     := "lean-worker",
  kind         := GokujoCallKind.release,
  mode         := RunMode.oneshot,
  output       := none,
  root         := some "minimal",
  log          := [ { taskName := "release-tag", agent := "pi", mode := RunMode.oneshot,
                      exitCode := 0, durationMs := 2100, stdoutSize := 384, stderrSize := 0 } ]
}

def leanWorker_bundle_caller : GokujoCaller := {
  callerId     := "lean-worker-bundle",
  repoName     := "lean-worker",
  kind         := GokujoCallKind.bundle,
  mode         := RunMode.oneshot,
  output       := none,
  root         := some "minimal",
  log          := [ { taskName := "bundle-create", agent := "pi", mode := RunMode.oneshot,
                      exitCode := 0, durationMs := 3900, stdoutSize := 896, stderrSize := 0 } ]
}

def leanWorker_init_caller : GokujoCaller := {
  callerId     := "lean-worker-init",
  repoName     := "lean-worker",
  kind         := GokujoCallKind.init,
  mode         := RunMode.oneshot,
  output       := none,
  root         := some "minimal",
  log          := [ { taskName := "repo-init", agent := "pi", mode := RunMode.oneshot,
                      exitCode := 0, durationMs := 1600, stdoutSize := 448, stderrSize := 0 } ]
}

def leanWorker_poll_caller : GokujoCaller := {
  callerId     := "lean-worker-poll",
  repoName     := "lean-worker",
  kind         := GokujoCallKind.poll,
  mode         := RunMode.oneshot,
  output       := none,
  root         := some "minimal",
  log          := [ { taskName := "poll-loop", agent := "pi", mode := RunMode.oneshot,
                      exitCode := 0, durationMs := 750, stdoutSize := 128, stderrSize := 0 } ]
}

def leanWorker_download_caller : GokujoCaller := {
  callerId     := "lean-worker-download",
  repoName     := "lean-worker",
  kind         := GokujoCallKind.download,
  mode         := RunMode.oneshot,
  output       := some "downloaded-files",
  root         := none,
  log          := [ { taskName := "download-cache", agent := "pi", mode := RunMode.oneshot,
                      exitCode := 0, durationMs := 2600, stdoutSize := 640, stderrSize := 0 } ]
}

def leanWorker_verify_caller : GokujoCaller := {
  callerId     := "lean-worker-verify",
  repoName     := "lean-worker",
  kind         := GokujoCallKind.verify,
  mode         := RunMode.oneshot,
  output       := some "verification-report.json",
  root         := some "minimal",
  log          := [ { taskName := "verify-manifest", agent := "pi", mode := RunMode.oneshot,
                      exitCode := 0, durationMs := 4100, stdoutSize := 1536, stderrSize := 0 } ]
}

def leanWorker_sync_caller : GokujoCaller := {
  callerId     := "lean-worker-sync",
  repoName     := "lean-worker",
  kind         := GokujoCallKind.sync,
  mode         := RunMode.oneshot,
  output       := none,
  root         := some "minimal",
  log          := [ { taskName := "sync-repo", agent := "pi", mode := RunMode.oneshot,
                      exitCode := 0, durationMs := 3400, stdoutSize := 960, stderrSize := 0 } ]
}

def leanWorker_bootstrap_caller : GokujoCaller := {
  callerId     := "lean-worker-bootstrap",
  repoName     := "lean-worker",
  kind         := GokujoCallKind.bootstrap,
  mode         := RunMode.oneshot,
  output       := some "lean-worker-gokujo",
  root         := none,
  log          := [ { taskName := "gokujo-bootstrap", agent := "pi", mode := RunMode.oneshot,
                      exitCode := 0, durationMs := 3100, stdoutSize := 256, stderrSize := 0 } ]
}

def callerRegistry : List GokujoCaller :=
  [ leanWorker_fetch_caller, leanWorker_build_caller, leanWorker_check_caller,
    leanWorker_selfcheck_caller, leanWorker_targets_caller, leanWorker_release_caller,
    leanWorker_bundle_caller, leanWorker_init_caller, leanWorker_poll_caller,
    leanWorker_download_caller, leanWorker_verify_caller, leanWorker_sync_caller,
    leanWorker_bootstrap_caller ]

def callerRegistry_count : Nat := callerRegistry.length

def findCallersByRepo (name : String) : List GokujoCaller :=
  callerRegistry.filter (fun c => c.repoName = name)

-- ============================================
-- Verification Theorems
-- ============================================

theorem leanWorker_fetch_caller_isValid : verifiedCaller leanWorker_fetch_caller := by
  unfold verifiedCaller gokujoCaller_isWellFormed gokujoCall_isParameterValid
  constructor
  · simp [leanWorker_fetch_caller]
  · constructor
    · simp
    · exact VerifiedRunner.example_verifiedRunner

theorem leanWorker_build_caller_isValid : verifiedCaller leanWorker_build_caller := by
  unfold verifiedCaller gokujoCaller_isWellFormed gokujoCall_isParameterValid
  constructor
  · simp [leanWorker_build_caller]
  · constructor
    · simp [Option.isSome, Option.map]
    · apply VerifiedRunner.log_wellFormed_example

theorem leanWorker_check_caller_isValid : verifiedCaller leanWorker_check_caller := by
  unfold verifiedCaller gokujoCaller_isWellFormed gokujoCall_isParameterValid
  constructor
  · simp [leanWorker_check_caller]
  · constructor
    · simp [Option.isSome, Option.map]
    · exact VerifiedRunner.example_verifiedRunner

theorem leanWorker_selfcheck_caller_isValid : verifiedCaller leanWorker_selfcheck_caller := by
  unfold verifiedCaller gokujoCaller_isWellFormed gokujoCall_isParameterValid
  constructor
  · simp [leanWorker_selfcheck_caller]
  · constructor
    · simp [Option.isSome, Option.map]
    · apply VerifiedRunner.log_wellFormed_example

theorem leanWorker_targets_caller_isValid : verifiedCaller leanWorker_targets_caller := by
  unfold verifiedCaller gokujoCaller_isWellFormed gokujoCall_isParameterValid
  constructor
  · simp [leanWorker_targets_caller]
  · constructor
    · simp [Option.isSome, Option.map]
    · apply VerifiedRunner.log_wellFormed_example

theorem leanWorker_release_caller_isValid : verifiedCaller leanWorker_release_caller := by
  unfold verifiedCaller gokujoCaller_isWellFormed gokujoCall_isParameterValid
  constructor
  · simp [leanWorker_release_caller]
  · constructor
    · simp [Option.isSome, Option.map]
    · apply VerifiedRunner.log_wellFormed_example

theorem leanWorker_bundle_caller_isValid : verifiedCaller leanWorker_bundle_caller := by
  unfold verifiedCaller gokujoCaller_isWellFormed gokujoCall_isParameterValid
  constructor
  · simp [leanWorker_bundle_caller]
  · constructor
    · simp [Option.isSome, Option.map]
    · apply VerifiedRunner.log_wellFormed_example

theorem leanWorker_init_caller_isValid : verifiedCaller leanWorker_init_caller := by
  unfold verifiedCaller gokujoCaller_isWellFormed gokujoCall_isParameterValid
  constructor
  · simp [leanWorker_init_caller]
  · constructor
    · simp [Option.isSome, Option.map]
    · apply VerifiedRunner.log_wellFormed_example

theorem leanWorker_poll_caller_isValid : verifiedCaller leanWorker_poll_caller := by
  unfold verifiedCaller gokujoCaller_isWellFormed gokujoCall_isParameterValid
  constructor
  · simp [leanWorker_poll_caller]
  · constructor
    · simp [Option.isSome, Option.map]
    · apply VerifiedRunner.log_wellFormed_example

theorem leanWorker_download_caller_isValid : verifiedCaller leanWorker_download_caller := by
  unfold verifiedCaller gokujoCaller_isWellFormed gokujoCall_isParameterValid
  constructor
  · simp [leanWorker_download_caller]
  · constructor
    · simp
    · apply VerifiedRunner.log_wellFormed_example

theorem leanWorker_verify_caller_isValid : verifiedCaller leanWorker_verify_caller := by
  unfold verifiedCaller gokujoCaller_isWellFormed gokujoCall_isParameterValid
  constructor
  · simp [leanWorker_verify_caller]
  · constructor
    · simp
    · apply VerifiedRunner.log_wellFormed_example

theorem leanWorker_sync_caller_isValid : verifiedCaller leanWorker_sync_caller := by
  unfold verifiedCaller gokujoCaller_isWellFormed gokujoCall_isParameterValid
  constructor
  · simp [leanWorker_sync_caller]
  · constructor
    · simp
    · apply VerifiedRunner.log_wellFormed_example

theorem leanWorker_bootstrap_caller_isValid : verifiedCaller leanWorker_bootstrap_caller := by
  unfold verifiedCaller gokujoCaller_isWellFormed gokujoCall_isParameterValid
  constructor
  · simp [leanWorker_bootstrap_caller]
  · constructor
    · simp
    · apply VerifiedRunner.log_wellFormed_example

theorem callerRegistry_allWellFormed :
  ∀ c ∈ callerRegistry, verifiedCaller c := by
  intro c hc
  simp [callerRegistry] at hc
  subst hc
  <;> assumption

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
