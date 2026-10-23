import RequestProject.Dasein15VM.Hecke
import RequestProject.Dasein15VM.Walk

/-!
# The Dasein15 walk continued with Hecke arguments

* `dasein_heckeCorrect`: the 500-state Dasein15 walk is a correct Hecke run (all arguments `0`)
  under **every** policy, by `HeckeCorrect.of_VMCorrect`.
* `heckePolicy23`: allows `T_2` and `T_3`, with total budget 3.
* `heckeArgs`: the arguments `[T_2, 0, T_3, T_2]`, continuing the walk from its final state
  `sFinal` (step 499) for four more steps.
* `checkHeckeTrace_ext`: the four-step continuation `heckeTrace` passes the Hecke trace checker
  (`decide +kernel`), so `heckeExt_correct` and kernel `Evidence` for it.
* `heckeRun_ext`: `heckeRun` produces exactly that trace (via `heckeRun_of_chain`).
* `heckeExt_final`: the end state has mass `66 = 63 + 3`, is still Spoke, and its Gödel number is
  `75 · sFinal.config` (the three Hecke factors `2 · 3 · 2 = 12` went in, and the elevator moved
  them up to `3 · 5² = 75`).
* `heckeRun_ext_conserve`: under `HeckePolicy.conserve` the same arguments are rejected at the
  first step.
-/

namespace Dasein15VM

open Dasein15 SpectrumVM

/-- Every Dasein15 walk state is also a Hecke run with zero arguments, under any policy. -/
theorem dasein_heckeCorrect (P : HeckePolicy 15) :
    HeckeCorrect daseinSpec P s₀ sFinal (List.replicate 499 0) daseinTrace := by
  have := HeckeCorrect.of_VMCorrect P dasein_VMCorrect
  rwa [daseinTrace_length] at this

/-- The policy allowing `T_2` and `T_3`, with total budget 3. -/
def heckePolicy23 : HeckePolicy 15 := ⟨fun i => decide (i.val < 2), 3⟩

/-- Hecke arguments for four more steps: `T_2`, nothing, `T_3`, `T_2`. -/
def heckeArgs : List (HeckeArg 15) := [HeckeArg.T 0, 0, HeckeArg.T 1, HeckeArg.T 0]

/-- The final state of the continuation (step 503). -/
def heckeFinal : VMState 15 := daseinSpec.ofShape (vec [0, 1, 2, 0, 0, 0, 0, 0, 0, 11, 48, 1, 1, 1, 1]) 503

/-- The five states of the continuation (steps 499–503). -/
def heckeTrace : List (VMState 15) :=
  [sFinal,
   daseinSpec.ofShape (vec [0, 1, 0, 0, 0, 0, 0, 0, 0, 11, 48, 1, 1, 1, 1]) 500,
   daseinSpec.ofShape (vec [0, 0, 1, 0, 0, 0, 0, 0, 0, 11, 48, 1, 1, 1, 1]) 501,
   daseinSpec.ofShape (vec [0, 0, 2, 0, 0, 0, 0, 0, 0, 11, 48, 1, 1, 1, 1]) 502,
   heckeFinal]

/-- The continuation passes the Hecke trace checker (kernel replay). -/
theorem checkHeckeTrace_ext :
    checkHeckeTrace daseinSpec heckePolicy23 sFinal heckeFinal heckeArgs heckeTrace = true := by
  decide +kernel

/-- **The continuation with Hecke arguments is a correct Hecke run.** -/
theorem heckeExt_correct :
    HeckeCorrect daseinSpec heckePolicy23 sFinal heckeFinal heckeArgs heckeTrace :=
  checkHeckeTrace_sound _ _ _ _ _ _ checkHeckeTrace_ext

/-- Kernel-established evidence for the continuation. -/
def heckeExtEvidence (claim : VerificationClaim) :
    Evidence (HeckeCorrect daseinSpec heckePolicy23 sFinal heckeFinal heckeArgs heckeTrace) :=
  heckeTraceEvidence _ _ _ _ _ _ checkHeckeTrace_ext claim

theorem heckeExtEvidence_assurance (claim : VerificationClaim) :
    (heckeExtEvidence claim).assurance = .kernelEstablished := rfl

/-- `heckeRun` produces exactly `heckeTrace`. -/
theorem heckeRun_ext : heckeRun daseinSpec heckePolicy23 heckeArgs sFinal = some heckeTrace :=
  heckeRun_of_chain _ _ heckeExt_correct.2.2.1 heckeExt_correct.1

/-- The end state: mass `66 = 63 + 3`, still Spoke, Gödel number `75 · sFinal.config`. -/
theorem heckeExt_final :
    mass heckeFinal.shape = 63 + totalArgMass heckeArgs ∧ totalArgMass heckeArgs = 3 ∧
      heckeFinal.cls = .Spoke ∧ heckeFinal.config = 75 * sFinal.config := by
  refine ⟨heckeExt_correct.final_invariant.mass_eq, ?_, ?_, ?_⟩ <;> decide +kernel

/-- Under the conserving policy the same arguments are rejected at the first step. -/
theorem heckeRun_ext_conserve :
    heckeRun daseinSpec HeckePolicy.conserve heckeArgs sFinal = none := by
  have : (HeckePolicy.conserve : HeckePolicy 15).admits (HeckeArg.T 0) = false := by
    rw [HeckePolicy.admits_T]; rfl
  simp [heckeArgs, heckeRun, heckeStep_not_admits _ this]

end Dasein15VM
