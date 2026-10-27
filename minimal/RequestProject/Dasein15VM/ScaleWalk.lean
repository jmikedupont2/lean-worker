import RequestProject.Dasein15VM.Scale
import RequestProject.Dasein15VM.Walk

/-!
# The Dasein15 walk continued with scale arguments

* `dasein_scaleCorrect`: the 500-state Dasein15 walk is a correct scaled run (all arguments `0`)
  under **every** policy, by `ScaleCorrect.of_VMCorrect`.
* `scalePolicy23`: allows prime `2` and prime `3`, with total budget 3.
* `scaleArgs`: the arguments `[×2, ×1, ×3, ×2]` (multipliers `2`, none, `3`, `2`), continuing the walk from its final state
  `sFinal` (step 499) for four more steps.
* `checkScaleTrace_ext`: the four-step continuation `scaleTrace` passes the scale trace checker
  (`decide +kernel`), so `scaleExt_correct` and kernel `Evidence` for it.
* `scaleRun_ext`: `scaleRun` produces exactly that trace (via `scaleRun_of_chain`).
* `scaleExt_final`: the end state has mass `66 = 63 + 3`, is still Spoke, and its Gödel number is
  `75 · sFinal.config` (the three multiplier factors `2 · 3 · 2 = 12` went in, and the elevator moved
  them up to `3 · 5² = 75`).
* `scaleRun_ext_conserve`: under `ScalePolicy.conserve` the same arguments are rejected at the
  first step.
-/

namespace Dasein15VM

open Dasein15 SpectrumVM

/-- Every Dasein15 walk state is also a scaled run with zero arguments, under any policy. -/
theorem dasein_scaleCorrect (P : ScalePolicy 15) :
    ScaleCorrect daseinSpec P s₀ sFinal (List.replicate 499 0) daseinTrace := by
  have := ScaleCorrect.of_VMCorrect P dasein_VMCorrect
  rwa [daseinTrace_length] at this

/-- The policy allowing prime `2` and prime `3`, with total budget 3. -/
def scalePolicy23 : ScalePolicy 15 := ⟨fun i => decide (i.val < 2), 3⟩

/-- Scale arguments for four more steps: prime `2`, no scaling, prime `3`, prime `2`. -/
def scaleArgs : List (ScaleArg 15) := [ScaleArg.unit 0, 0, ScaleArg.unit 1, ScaleArg.unit 0]

/-- The final state of the continuation (step 503). -/
def scaleFinal : VMState 15 := daseinSpec.ofShape (vec [0, 1, 2, 0, 0, 0, 0, 0, 0, 11, 48, 1, 1, 1, 1]) 503

/-- The five states of the continuation (steps 499–503). -/
def scaleTrace : List (VMState 15) :=
  [sFinal,
   daseinSpec.ofShape (vec [0, 1, 0, 0, 0, 0, 0, 0, 0, 11, 48, 1, 1, 1, 1]) 500,
   daseinSpec.ofShape (vec [0, 0, 1, 0, 0, 0, 0, 0, 0, 11, 48, 1, 1, 1, 1]) 501,
   daseinSpec.ofShape (vec [0, 0, 2, 0, 0, 0, 0, 0, 0, 11, 48, 1, 1, 1, 1]) 502,
   scaleFinal]

/-- The continuation passes the scale trace checker (kernel replay). -/
theorem checkScaleTrace_ext :
    checkScaleTrace daseinSpec scalePolicy23 sFinal scaleFinal scaleArgs scaleTrace = true := by
  decide +kernel

/-- **The continuation with scale arguments is a correct scaled run.** -/
theorem scaleExt_correct :
    ScaleCorrect daseinSpec scalePolicy23 sFinal scaleFinal scaleArgs scaleTrace :=
  checkScaleTrace_sound _ _ _ _ _ _ checkScaleTrace_ext

/-- Kernel-established evidence for the continuation. -/
def scaleExtEvidence (claim : VerificationClaim) :
    Evidence (ScaleCorrect daseinSpec scalePolicy23 sFinal scaleFinal scaleArgs scaleTrace) :=
  scaleTraceEvidence _ _ _ _ _ _ checkScaleTrace_ext claim

theorem scaleExtEvidence_assurance (claim : VerificationClaim) :
    (scaleExtEvidence claim).assurance = .kernelEstablished := rfl

/-- `scaleRun` produces exactly `scaleTrace`. -/
theorem scaleRun_ext : scaleRun daseinSpec scalePolicy23 scaleArgs sFinal = some scaleTrace :=
  scaleRun_of_chain _ _ scaleExt_correct.2.2.1 scaleExt_correct.1

/-- The end state: mass `66 = 63 + 3`, still Spoke, Gödel number `75 · sFinal.config`. -/
theorem scaleExt_final :
    mass scaleFinal.shape = 63 + totalArgMass scaleArgs ∧ totalArgMass scaleArgs = 3 ∧
      scaleFinal.cls = .Spoke ∧ scaleFinal.config = 75 * sFinal.config := by
  refine ⟨scaleExt_correct.final_invariant.mass_eq, ?_, ?_, ?_⟩ <;> decide +kernel

/-- Under the conserving policy the same arguments are rejected at the first step. -/
theorem scaleRun_ext_conserve :
    scaleRun daseinSpec ScalePolicy.conserve scaleArgs sFinal = none := by
  have : (ScalePolicy.conserve : ScalePolicy 15).admits (ScaleArg.unit 0) = false := by
    rw [ScalePolicy.admits_unit]; rfl
  simp [scaleArgs, scaleRun, scaleStep_not_admits _ this]

end Dasein15VM
