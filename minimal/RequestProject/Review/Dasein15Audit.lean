import RequestProject.Dasein15VM.Walk

/-!
# Audit of `Dasein15.lean`: statements that say less than their names or comments

Kernel-checked facts behind the items in `TODO.md` about the original `Dasein15.lean`.
Nothing in `Dasein15.lean` is changed. (The statement about mass conservation *along the walk*,
which `dasein_mass_conserved_63` does not make, is `Dasein15VM.dasein_mass_conserved`.)
-/

namespace Dasein15Audit

open Dasein15 Dasein15VM

/-- The conjunct "final state is pure SSP" in `dasein15_colosseum_result`,
`∀ i, finalExp i = 0 ∨ finalExp i ≥ 1`, holds for *every* exponent vector. -/
theorem pure_ssp_conjunct_tautology (v : Fin 15 → ℕ) : ∀ i, v i = 0 ∨ v i ≥ 1 :=
  fun i => by omega

/-- `finalGodel` is the total mass 63, not the Gödel number of the final state, so
`finalGodel_crt` and `finalGodel_crt_address` are facts about the number 63. -/
theorem finalGodel_is_not_godel : finalGodel = 63 ∧ finalGodel ≠ godel sspBasis finalExp := by
  refine ⟨by decide, ?_⟩
  decide +kernel

/-- No prime is assigned to `Clock` in Dasein15's `eigenspace`. -/
theorem clock_empty : ∀ i : Fin 15, eigenspace i ≠ .Clock := by decide

/-- The floor of the Euclidean norm of the initial shard is 34, so its Bott class is 2 (H).
The module header of `Dasein15.lean` says "Bott=1 (C)" for the initial state. -/
theorem initial_norm_floor :
    Nat.sqrt (∑ i, initShape i ^ 2) = 34 ∧ bottClass 34 = ⟨2, by omega⟩ := by
  refine ⟨?_, by decide⟩
  have h : ∑ i, initShape i ^ 2 = 1217 := by decide
  rw [h, eq_comm, Nat.eq_sqrt]
  norm_num

/-- The floor of the norm of the final state is 49 (Bott class 1). -/
theorem final_norm_floor :
    Nat.sqrt (∑ i, finalExp i ^ 2) = 49 ∧ bottClass 49 = ⟨1, by omega⟩ := by
  refine ⟨?_, by decide⟩
  have h : ∑ i, finalExp i ^ 2 = 2429 := by decide
  rw [h, eq_comm, Nat.eq_sqrt]
  norm_num

end Dasein15Audit
