import RequestProject.Dasein15VM.VM
import RequestProject.Dasein15VM.TraceData

/-!
# Dasein15 VM: the Dasein15 walk as a certified VM trace

* `daseinSpec`: the VM instance (15 supersingular primes, Dasein15's `eigenspace`, the cyclic
  elevator for every class, conserved mass 63).
* `checkVMTrace_dasein`: the 500-state trace (steps 0–499) passes the trace checker, by
  `decide +kernel`; hence `dasein_VMCorrect` and kernel `Evidence` for it.
* `dasein_phases`: the shape-class trajectory of the trace changes exactly at steps
  0, 255, 314, 421 with classes Earth, Spoke, Hub, Spoke — Dasein15's `daseinPhases`.
* `dasein_fractranRun`: 499 FRACTRAN steps of Dasein15's own program `daseinFrac` take the
  initial shard to `29^11 * 31^48 * 41 * 47 * 59 * 71`, whose exponent vector is `finalExp`.
* `dasein_mass_conserved`: for every `k`, the `k`-step run succeeds and has total mass 63.
-/

namespace Dasein15VM

open Dasein15 SpectrumVM

/-- The Dasein15 instance of the VM. -/
def daseinSpec : VMSpec 15 where
  basis := sspBasis
  assign := eigenspace
  route := fun _ => elevator
  route_ne := fun _ => elevator_ne
  mass := 63

/-- Read a shape from an exponent list. -/
def vec (l : List ℕ) : PrimeShape 15 := fun i => l.getD i 0

/-- The initial shard: exponents 25, 24, 2 on 2, 3, 5 and 1 on the other twelve primes. -/
def initShape : PrimeShape 15 := fun i => match i with
  | 0 => 25 | 1 => 24 | 2 => 2 | _ => 1

/-- Initial VM state. -/
def s₀ : VMState 15 := daseinSpec.ofShape initShape 0

/-- Final VM state, after 499 steps. -/
def sFinal : VMState 15 := daseinSpec.ofShape finalExp 499

/-- The 500-state trace (steps 0–499). -/
def daseinTrace : List (VMState 15) :=
  (daseinShapes.zipIdx).map fun p => daseinSpec.ofShape (vec p.1) p.2

theorem daseinTrace_length : daseinTrace.length = 500 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The trace passes the trace checker (kernel replay). -/
theorem checkVMTrace_dasein : checkVMTrace daseinSpec s₀ sFinal daseinTrace = true := by
  decide +kernel

/-- **The Dasein15 walk is a correct VM trace.** -/
theorem dasein_VMCorrect : VMCorrect daseinSpec s₀ sFinal daseinTrace :=
  checkVMTrace_sound _ _ _ _ checkVMTrace_dasein

/-- Kernel-established evidence for the walk. -/
def daseinEvidence (claim : VerificationClaim) :
    Evidence (VMCorrect daseinSpec s₀ sFinal daseinTrace) :=
  traceEvidence _ _ _ _ checkVMTrace_dasein claim

theorem daseinEvidence_assurance (claim : VerificationClaim) :
    (daseinEvidence claim).assurance = .kernelEstablished := rfl

/-- Phase starts of a class sequence: each position whose class differs from its predecessor. -/
def phaseStarts (l : List ShapeClass) : List (ShapeClass × ℕ) :=
  l.zipIdx.filter fun p => p.2 = 0 ∨ l[p.2 - 1]? ≠ some p.1

/-- The shape-class trajectory of the walk matches Dasein15's four observed phases. -/
theorem dasein_phases :
    phaseStarts (daseinTrace.map VMState.cls) =
      daseinPhases.map fun p => (p.dominant, p.startStep) := by
  decide +kernel

theorem dasein_trajectory :
    (phaseStarts (daseinTrace.map VMState.cls)).map Prod.fst = [.Earth, .Spoke, .Hub, .Spoke] := by
  rw [dasein_phases]; decide

theorem sFinal_shape : sFinal.shape = finalExp := rfl

theorem sFinal_cls : sFinal.cls = .Spoke := by decide +kernel

theorem sFinal_config : sFinal.config = 29 ^ 11 * 31 ^ 48 * 41 * 47 * 59 * 71 := by decide +kernel

theorem s₀_config :
    s₀.config = 2 ^ 25 * 3 ^ 24 * 5 ^ 2 * 7 * 11 * 13 * 17 * 19 * 23 * 29 * 31 * 41 * 47 * 59 * 71 := by
  decide +kernel

/-- **499 FRACTRAN steps of Dasein15's program** take the initial shard to
`29^11 * 31^48 * 41 * 47 * 59 * 71`. -/
theorem dasein_fractranRun :
    fractranRun (List.ofFn daseinFrac) 499
        (2 ^ 25 * 3 ^ 24 * 5 ^ 2 * 7 * 11 * 13 * 17 * 19 * 23 * 29 * 31 * 41 * 47 * 59 * 71) =
      some (29 ^ 11 * 31 ^ 48 * 41 * 47 * 59 * 71) := by
  have h := dasein_VMCorrect.fractranRun (τ := elevator) (fun _ => rfl)
  rw [daseinTrace_length, s₀_config, sFinal_config] at h
  rw [← routeProg_elevator]
  exact h

/-- The exponent vector of the step-499 FRACTRAN state is Dasein15's `finalExp`. -/
theorem sspExp_final : sspExp (29 ^ 11 * 31 ^ 48 * 41 * 47 * 59 * 71) = finalExp := by
  rw [← sFinal_config, sFinal, VMSpec.ofShape, ← shapeOf_sspBasis]
  exact shapeOf_godel _ _

/-- **Unbounded mass conservation**: for every `k`, `k` FRACTRAN steps of `daseinFrac` from the
initial shard succeed, and the resulting number has total SSP exponent 63 (it is the Gödel number
of its shape, so it has no other prime factors). -/
theorem dasein_mass_conserved (k : ℕ) :
    ∃ c, fractranRun (List.ofFn daseinFrac) k
        (2 ^ 25 * 3 ^ 24 * 5 ^ 2 * 7 * 11 * 13 * 17 * 19 * 23 * 29 * 31 * 41 * 47 * 59 * 71) =
        some c ∧ totalMass (sspExp c) = 63 ∧ c = godel sspBasis (sspExp c) := by
  obtain ⟨w, hw, hm⟩ := fractranRun_routeProg_mass sspBasis elevator elevator_ne k initShape
    (by decide)
  refine ⟨godel sspBasis w, ?_, ?_, ?_⟩
  · rw [← routeProg_elevator, ← s₀_config]; exact hw
  · rw [← shapeOf_sspBasis, shapeOf_godel, ← mass_dasein, hm]; decide
  · rw [← shapeOf_sspBasis, shapeOf_godel]

/-- **Colosseum result, grounded in the run.** The FRACTRAN state reached after 499 steps of
`daseinFrac` from the initial shard has exponent vector `finalExp`: total mass 63, pure SSP,
Spoke mass 62, Earth mass 1, and dominant shape class Spoke. -/
theorem dasein15_colosseum_from_vm :
    ∃ c, fractranRun (List.ofFn daseinFrac) 499
        (2 ^ 25 * 3 ^ 24 * 5 ^ 2 * 7 * 11 * 13 * 17 * 19 * 23 * 29 * 31 * 41 * 47 * 59 * 71) =
        some c ∧ sspExp c = finalExp ∧ totalMass (sspExp c) = 63 ∧
      eigenMass .Spoke (sspExp c) = 62 ∧ eigenMass .Earth (sspExp c) = 1 ∧
      shapeClass eigenspace (sspExp c) = .Spoke :=
  ⟨_, dasein_fractranRun, sspExp_final, by rw [sspExp_final]; decide,
    by rw [sspExp_final]; decide, by rw [sspExp_final]; decide, by rw [sspExp_final]; decide⟩

end Dasein15VM
