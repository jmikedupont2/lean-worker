import RequestProject.Dasein15VM.Walk

/-!
# Dasein15 VM: an honest path for untrusted traces

The original trust layer only ever produced `kernelEstablished` evidence. This file gives
untrusted inputs a real path through SpectrumVM's assurance levels:

* `checkVMTrace_complete`: the trace checker is *complete* as well as sound, so
  `checkVMTrace_iff : checkVMTrace S s₀ s tr = true ↔ VMCorrect S s₀ s tr`, and `VMCorrect` is
  decidable.
* `importTrace`: a trace received from outside carries only `external` evidence.
* `ingestTrace`: runs the (compiled) checker on an imported trace. If the checker accepts, the
  evidence is `soundChecker` (there is a soundness theorem, but this execution was not replayed in
  the kernel); otherwise it stays `external`. `ingestTrace` never reports `kernelEstablished`, and
  it reports `soundCheckerExecution` exactly when the trace is correct
  (`ingestTrace_soundChecker_iff`).
* `replayTrace`: the only way to reach `kernelEstablished` — it needs a closed proof that the
  checker accepts (in practice `decide +kernel`).
* A tampered copy of the Dasein15 walk (one state deleted) is rejected: it is not a correct trace
  (`tampered_not_correct`), so no evidence for it can be kernel-established, and ingesting it
  yields only `external` evidence.
-/

namespace Dasein15VM

open SpectrumVM (Evidence Assurance VerificationClaim)

variable {n : ℕ}

/-- The chain checker is complete. -/
theorem checkChain_complete (S : VMSpec n) :
    ∀ (l : List (VMState n)), (∀ i (h : i + 1 < l.length), step S l[i] = some l[i + 1]) →
      checkChain S l = true
  | [], _ => rfl
  | [_], _ => rfl
  | s :: t :: rest, h => by
    simp only [checkChain, Bool.and_eq_true]
    refine ⟨(checkStep_iff S s t).2 (h 0 (by simp)), checkChain_complete S (t :: rest) ?_⟩
    intro i hi
    exact h (i + 1) (by simp at hi ⊢; omega)

/-- **Trace checker completeness.** -/
theorem checkVMTrace_complete (S : VMSpec n) (s₀ s : VMState n) (tr : List (VMState n))
    (h : VMCorrect S s₀ s tr) : checkVMTrace S s₀ s tr = true := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  simp only [checkVMTrace, h0, h1, (stateBEq_iff _ _).2, checkChain_complete S tr h2,
    Bool.and_eq_true, List.all_eq_true, and_true, true_and]
  exact fun s' hs' => (checkVMInvariant_iff S s').2 (h3 s' hs')

/-- The trace checker decides trace correctness. -/
theorem checkVMTrace_iff (S : VMSpec n) (s₀ s : VMState n) (tr : List (VMState n)) :
    checkVMTrace S s₀ s tr = true ↔ VMCorrect S s₀ s tr :=
  ⟨checkVMTrace_sound S s₀ s tr, checkVMTrace_complete S s₀ s tr⟩

instance (S : VMSpec n) (s₀ s : VMState n) (tr : List (VMState n)) :
    Decidable (VMCorrect S s₀ s tr) :=
  decidable_of_iff _ (checkVMTrace_iff S s₀ s tr)

/-- An imported trace: where it came from, and what it claims. -/
structure TraceReport (n : ℕ) where
  source : String
  start : VMState n
  final : VMState n
  trace : List (VMState n)

/-- Importing a trace yields only `external` evidence. -/
def importTrace (r : TraceReport n) (S : VMSpec n) : Evidence (VMCorrect S r.start r.final r.trace) :=
  .external r.source "imported VM trace (not checked)"

/-- Run the checker (at run time) on an imported trace. Acceptance yields `soundChecker`
evidence; rejection leaves the trace `external`. -/
def ingestTrace (S : VMSpec n) (r : TraceReport n) (claim : VerificationClaim) :
    Evidence (VMCorrect S r.start r.final r.trace) :=
  if checkVMTrace S r.start r.final r.trace then .soundChecker claim
  else .external r.source "VM trace rejected by checkVMTrace"

/-- Kernel replay: the only route to `kernelEstablished`, requiring a closed proof that the
checker accepts. -/
def replayTrace (S : VMSpec n) (r : TraceReport n) (h : checkVMTrace S r.start r.final r.trace = true)
    (claim : VerificationClaim) : Evidence (VMCorrect S r.start r.final r.trace) :=
  traceEvidence S r.start r.final r.trace h claim

theorem importTrace_assurance (r : TraceReport n) (S : VMSpec n) :
    (importTrace r S).assurance = .external := rfl

theorem replayTrace_assurance (S : VMSpec n) (r : TraceReport n)
    (h : checkVMTrace S r.start r.final r.trace = true) (claim : VerificationClaim) :
    (replayTrace S r h claim).assurance = .kernelEstablished := rfl

/-- Run-time ingestion never claims kernel assurance. -/
theorem ingestTrace_ne_kernel (S : VMSpec n) (r : TraceReport n) (claim : VerificationClaim) :
    (ingestTrace S r claim).assurance ≠ .kernelEstablished := by
  unfold ingestTrace
  split <;> simp [Evidence.assurance]

/-- **The sound-checker label is exact**: ingestion reports `soundCheckerExecution` iff the
imported trace is a correct VM trace. -/
theorem ingestTrace_soundChecker_iff (S : VMSpec n) (r : TraceReport n) (claim : VerificationClaim) :
    (ingestTrace S r claim).assurance = .soundCheckerExecution ↔
      VMCorrect S r.start r.final r.trace := by
  refine Iff.trans ?_ (checkVMTrace_iff S r.start r.final r.trace)
  unfold ingestTrace
  split <;> simp_all [Evidence.assurance]

/-- Ingestion of an incorrect trace stays `external`. -/
theorem ingestTrace_external_of_not_correct (S : VMSpec n) (r : TraceReport n)
    (claim : VerificationClaim) (h : ¬ VMCorrect S r.start r.final r.trace) :
    (ingestTrace S r claim).assurance = .external := by
  rw [← checkVMTrace_iff] at h
  unfold ingestTrace
  simp [h, Evidence.assurance]

/-- No evidence for an incorrect trace can be kernel-established. -/
theorem not_kernel_of_not_correct {S : VMSpec n} {s₀ s : VMState n} {tr : List (VMState n)}
    (h : ¬ VMCorrect S s₀ s tr) (e : Evidence (VMCorrect S s₀ s tr)) :
    e.assurance ≠ .kernelEstablished := fun he => h (e.sound he)

/-! ### The Dasein15 walk: genuine and tampered reports -/

/-- The Dasein15 walk as an imported report. -/
def daseinReport : TraceReport 15 := ⟨"Dasein15 walk (500 states)", s₀, sFinal, daseinTrace⟩

/-- The Dasein15 walk with the state at step 250 deleted. -/
def tamperedReport : TraceReport 15 :=
  ⟨"Dasein15 walk, step 250 deleted", s₀, sFinal, daseinTrace.eraseIdx 250⟩

set_option maxRecDepth 100000 in
theorem checkVMTrace_tampered :
    checkVMTrace daseinSpec tamperedReport.start tamperedReport.final tamperedReport.trace = false := by
  decide +kernel

/-- The tampered walk is not a correct VM trace. -/
theorem tampered_not_correct :
    ¬ VMCorrect daseinSpec tamperedReport.start tamperedReport.final tamperedReport.trace := by
  rw [← checkVMTrace_iff, checkVMTrace_tampered]; decide

/-- Ingesting the tampered walk yields only `external` evidence. -/
theorem ingest_tampered (claim : VerificationClaim) :
    (ingestTrace daseinSpec tamperedReport claim).assurance = .external :=
  ingestTrace_external_of_not_correct _ _ _ tampered_not_correct

/-- The genuine walk is promoted to kernel evidence by replay. -/
def daseinReplayed (claim : VerificationClaim) :
    Evidence (VMCorrect daseinSpec daseinReport.start daseinReport.final daseinReport.trace) :=
  replayTrace daseinSpec daseinReport checkVMTrace_dasein claim

/-- Ingesting the genuine walk yields `soundChecker` evidence. -/
theorem ingest_dasein (claim : VerificationClaim) :
    (ingestTrace daseinSpec daseinReport claim).assurance = .soundCheckerExecution :=
  (ingestTrace_soundChecker_iff _ _ _).2 dasein_VMCorrect

end Dasein15VM
