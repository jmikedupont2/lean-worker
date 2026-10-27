import RequestProject.Cryptids.Funnel
import RequestProject.Cryptids.Duel
import RequestProject.Dasein15VM.Walk

/-!
# Cryptids, part 3: FRACTRAN meters visit the Dasein15 walk

Three small FRACTRAN programs read the Dasein15 VM using nothing but FRACTRAN:

* **Ω-meter** `omegaMeter = [2/3, 2/5, …, 2/71]` (the constant funnel): on the Gödel number of `v`
  it runs `mass v - v 0` steps and halts on `2 ^ mass v` (`omegaMeter_run`, `omegaMeter_halts`).
  Every state of the 500-step walk, and every state of the unbounded `daseinFrac` run, weighs
  exactly `2 ^ 63` (`omegaMeter_walk`, `omegaMeter_forever`).
* **class-meter** `classMeter` (the funnel "send each prime to the first prime of its class"):
  it halts on `2 ^ Earth * 17 ^ Spoke * 19 ^ Hub` (`classMeter_run`); kernel instances on the
  first and last state of the walk (`classMeter_s₀`, `classMeter_sFinal`).
* **Earth/Spoke duel** `duelProg 2 17`: fed the class-meter output it halts on
  `2 ^ (Earth - Spoke) * 17 ^ (Spoke - Earth) * 19 ^ Hub` (`earthSpoke_duel`): Earth wins the
  initial state by 49, Spoke wins the final state by 61 (`duel_s₀`, `duel_sFinal`).
-/

namespace Dasein15VM.Cryptids

open Dasein15 Dasein15VM Funnel

/-! ## The Ω-meter -/

/-- The constant funnel onto the prime `2`. -/
def omegaFunnel : Funnel 15 := ⟨fun _ => 0, fun _ => rfl⟩

/-- The Ω-meter: `[2/3, 2/5, 2/7, …, 2/71]`. -/
def omegaMeter : List ℚ := funnelProg sspBasis omegaFunnel

theorem omegaMeter_eq :
    omegaMeter = [2/3, 2/5, 2/7, 2/11, 2/13, 2/17, 2/19, 2/23, 2/29, 2/31, 2/41, 2/47, 2/59,
      2/71] := by
  simp [omegaMeter, funnelProg, Funnel.sources, omegaFunnel, List.finRange_succ, sspBasis, SSP]

theorem omegaFunnel_sourceMass (v : PrimeShape 15) : omegaFunnel.sourceMass v = mass v - v 0 := by
  have : omegaFunnel.sourceMass v + v 0 = mass v := by
    simp [Funnel.sourceMass, omegaFunnel, mass_eq_sum, Fin.sum_univ_succ (n := 14),
      add_comm]
    rfl
  omega

theorem godel_push_omega (v : PrimeShape 15) :
    godel sspBasis (push omegaFunnel.σ v) = 2 ^ mass v := by
  simp [godel_eq_prod, push, omegaFunnel, mass_eq_sum, sspBasis, SSP]

/-- **Ω-meter**: in `mass v - v 0` steps the Ω-meter turns the Gödel number of `v` into
`2 ^ mass v`. -/
theorem omegaMeter_run (v : PrimeShape 15) :
    fractranRun omegaMeter (mass v - v 0) (godel sspBasis v) = some (2 ^ mass v) := by
  rw [← godel_push_omega, ← omegaFunnel_sourceMass]
  exact omegaFunnel.funnel_run sspBasis _ v rfl

/-- The Ω-meter halts on every power of two. -/
theorem omegaMeter_halts (m : ℕ) : fractranStep omegaMeter (2 ^ m) = none := by
  have := omegaFunnel.funnel_halts sspBasis (fun i => if i = 0 then m else 0)
  rw [godel_push_omega] at this
  simpa [mass_eq_sum] using this

/-- **Every state of the walk weighs `2 ^ 63`.** -/
theorem omegaMeter_walk :
    ∀ s ∈ daseinTrace, fractranRun omegaMeter (63 - s.shape 0) s.config = some (2 ^ 63) := by
  intro s hs
  obtain ⟨h1, -, h3⟩ := dasein_VMCorrect.2.2.2 s hs
  rw [h1, show (63 : ℕ) = mass s.shape from h3.symm]
  exact omegaMeter_run _

/-- **Every state of the unbounded run weighs `2 ^ 63`.** -/
theorem omegaMeter_forever (k : ℕ) :
    ∃ c t, fractranRun (List.ofFn daseinFrac) k s₀.config = some c ∧
      fractranRun omegaMeter t c = some (2 ^ 63) := by
  obtain ⟨w, hw, hm⟩ := fractranRun_routeProg_mass sspBasis elevator elevator_ne k initShape
    (by decide)
  refine ⟨godel sspBasis w, mass w - w 0, ?_, ?_⟩
  · rw [← routeProg_elevator]; exact hw
  · rw [omegaMeter_run, hm]; rfl

/-! ## The class-meter -/

/-- The representative of each class: Earth ↦ 2, Spoke ↦ 17, Hub ↦ 19 (Clock, which has no
prime, is parked on 3). -/
def classRep : ShapeClass → Fin 15
  | .Earth => 0 | .Spoke => 6 | .Hub => 7 | .Clock => 1

theorem classRep_injective : Function.Injective classRep := by
  intro a b; cases a <;> cases b <;> decide

/-- The class funnel: each prime goes to the representative of its class. -/
def classFunnel : Funnel 15 := ⟨classRep ∘ eigenspace, by decide⟩

/-- The class-meter program. -/
def classMeter : List ℚ := funnelProg sspBasis classFunnel

theorem classMeter_eq :
    classMeter = [2/3, 2/5, 2/7, 2/11, 2/13, 19/23, 17/29, 17/31, 17/41, 2/47, 17/59, 17/71] := by
  simp [classMeter, funnelProg, Funnel.sources, classFunnel, classRep, eigenspace,
    List.finRange_succ, sspBasis, SSP]

theorem eigenMass_clock (v : PrimeShape 15) : eigenMass .Clock v = 0 :=
  Finset.sum_eq_zero fun i _ => by
    have : eigenspace i ≠ .Clock := by revert i; decide
    simp [this]

theorem push_class_apply (v : PrimeShape 15) (e : ShapeClass) :
    push classFunnel.σ v (classRep e) = eigenMass e v := by
  rw [← classMass_dasein]; exact push_classMass _ _ classRep_injective v e

theorem classFunnel_moves :
    ∀ i : Fin 15, i ≠ 0 → i ≠ 6 → i ≠ 7 → i ≠ 1 → classFunnel.σ i ≠ i := by decide

theorem godel_push_class (v : PrimeShape 15) :
    godel sspBasis (push classFunnel.σ v) =
      2 ^ eigenMass .Earth v * 17 ^ eigenMass .Spoke v * 19 ^ eigenMass .Hub v := by
  have hz : ∀ i, classFunnel.σ i ≠ i → push classFunnel.σ v i = 0 := fun i hi =>
    classFunnel.eq_zero_of_sourceMass_eq_zero (classFunnel.sourceMass_push v) hi
  have h0 := push_class_apply v .Earth
  have h6 := push_class_apply v .Spoke
  have h7 := push_class_apply v .Hub
  have h1 := push_class_apply v .Clock
  rw [eigenMass_clock] at h1
  simp only [classRep] at h0 h6 h7 h1
  have hw : push classFunnel.σ v = fun i => if i = 0 then eigenMass .Earth v else
      if i = 6 then eigenMass .Spoke v else if i = 7 then eigenMass .Hub v else 0 := by
    funext i
    split_ifs with a b c
    · subst a; exact h0
    · subst b; exact h6
    · subst c; exact h7
    · by_cases d : i = 1
      · subst d; exact h1
      · exact hz i (classFunnel_moves i a b c d)
  rw [hw]
  simp only [godel, List.ofFn_succ, List.ofFn_zero]
  simp [sspBasis, SSP, Fin.ext_iff]
  ring

/-- **Class-meter**: the class-meter turns the Gödel number of `v` into
`2 ^ Earth * 17 ^ Spoke * 19 ^ Hub` (and then halts, `classMeter_halts`). -/
theorem classMeter_run (v : PrimeShape 15) :
    fractranRun classMeter (classFunnel.sourceMass v) (godel sspBasis v) =
      some (2 ^ eigenMass .Earth v * 17 ^ eigenMass .Spoke v * 19 ^ eigenMass .Hub v) := by
  rw [← godel_push_class]; exact classFunnel.funnel_run sspBasis _ v rfl

theorem classMeter_halts (v : PrimeShape 15) :
    fractranStep classMeter
      (2 ^ eigenMass .Earth v * 17 ^ eigenMass .Spoke v * 19 ^ eigenMass .Hub v) = none := by
  rw [← godel_push_class]; exact classFunnel.funnel_halts sspBasis v

theorem classMeter_s₀ :
    fractranRun classMeter 36 s₀.config = some (2 ^ 55 * 17 ^ 6 * 19 ^ 2) := by
  have h := classMeter_run initShape
  have e1 : classFunnel.sourceMass initShape = 36 := by decide +kernel
  have e2 : eigenMass .Earth initShape = 55 := by decide +kernel
  have e3 : eigenMass .Spoke initShape = 6 := by decide +kernel
  have e4 : eigenMass .Hub initShape = 2 := by decide +kernel
  rw [e1, e2, e3, e4] at h
  exact h

theorem classMeter_sFinal :
    fractranRun classMeter 63 sFinal.config = some (2 ^ 1 * 17 ^ 62 * 19 ^ 0) := by
  have h := classMeter_run finalExp
  have e1 : classFunnel.sourceMass finalExp = 63 := by decide +kernel
  have e2 : eigenMass .Earth finalExp = 1 := by decide +kernel
  have e3 : eigenMass .Spoke finalExp = 62 := by decide +kernel
  have e4 : eigenMass .Hub finalExp = 0 := by decide +kernel
  rw [e1, e2, e3, e4] at h
  exact h

/-! ## The Earth/Spoke duel -/

theorem not_dvd_pow19 {p : ℕ} (hp : p.Prime) (h19 : p ≠ 19) (m : ℕ) : ¬ p ∣ 19 ^ m := fun h =>
  h19 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 (hp.dvd_of_dvd_pow h))

/-- **Earth/Spoke duel**: on the class-meter output, the duel `[1/34]` cancels Earth against
Spoke and halts on the survivor. -/
theorem earthSpoke_duel (E S H : ℕ) :
    fractranRun (duelProg 2 17) (min E S) (2 ^ E * 17 ^ S * 19 ^ H) =
        some (2 ^ (E - S) * 17 ^ (S - E) * 19 ^ H) ∧
      fractranStep (duelProg 2 17) (2 ^ (E - S) * 17 ^ (S - E) * 19 ^ H) = none :=
  ⟨duel_run (by norm_num) (by norm_num) _ E S,
    duel_halts (by norm_num) (by norm_num) (by norm_num) (not_dvd_pow19 (by norm_num)
      (by norm_num) H) (not_dvd_pow19 (by norm_num) (by norm_num) H) E S⟩

/-- Initial state: Earth beats Spoke by 49. -/
theorem duel_s₀ :
    fractranRun (duelProg 2 17) 6 (2 ^ 55 * 17 ^ 6 * 19 ^ 2) = some (2 ^ 49 * 19 ^ 2) := by
  simpa using (earthSpoke_duel 55 6 2).1

/-- Final state: Spoke beats Earth by 61. -/
theorem duel_sFinal :
    fractranRun (duelProg 2 17) 1 (2 ^ 1 * 17 ^ 62 * 19 ^ 0) = some (17 ^ 61) := by
  simpa using (earthSpoke_duel 1 62 0).1

end Dasein15VM.Cryptids
