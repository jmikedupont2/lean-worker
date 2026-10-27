import RequestProject.Dasein15VM.Fractran

/-!
# Cryptids, part 1: the funnel theorem (FRACTRAN computes pushforwards)

A *funnel* is a map `σ : Fin n → Fin n` with `σ ∘ σ = σ`: every coordinate is sent to a sink
(a fixed point of `σ`).  The *funnel program* `funnelProg B F` is the FRACTRAN program with one
fraction `p (σ i) / p i` for every non-sink `i` (in index order).

**Funnel theorem** (`funnel_run`, `funnel_halts`, `funnel_run_succ`): started on the Gödel number
of a shape `v`, the funnel program runs for exactly `sourceMass v` steps (the mass sitting on
non-sinks) and halts on the Gödel number of the pushforward `σ_* v`, where
`(σ_* v) j = ∑_{σ i = j} v i`.

So FRACTRAN *measures* shapes: with `σ` constant the output is `p₀ ^ mass v` (an Ω-meter), and
with `σ` = "send each prime to a representative of its class" the output exponents are the class
masses (a class-meter).
-/

namespace Dasein15VM.Cryptids

open Dasein15VM

variable {n : ℕ}

/-- FRACTRAN bridge for an arbitrary list of indices, each moved by `τ` to a different index. -/
theorem fractranStep_map_godel_of_mem (B : PrimeBasis n) (τ : Fin n → Fin n) (v : PrimeShape n) :
    ∀ (L : List (Fin n)), (∀ i ∈ L, τ i ≠ i) →
      fractranStep (L.map fun i => (B.p (τ i) : ℚ) / B.p i) (godel B v) =
        (L.find? fun i => 0 < v i).map fun i => godel B (moveUnit v i (τ i))
  | [], _ => rfl
  | i :: L, hL => by
    simp only [List.map_cons, fractranStep, List.find?_cons]
    have hi : τ i ≠ i := hL i (by simp)
    by_cases h : 0 < v i
    · rw [if_pos ((fractranFrac_godel B v hi).2 h), fractranFrac_godel_val B v _ h]
      simp [h]
    · rw [if_neg (mt (fractranFrac_godel B v hi).1 h),
        fractranStep_map_godel_of_mem B τ v L fun j hj => hL j (by simp [hj])]
      simp [h]

/-- A funnel: an idempotent map of coordinates. -/
structure Funnel (n : ℕ) where
  σ : Fin n → Fin n
  idem : ∀ i, σ (σ i) = σ i

namespace Funnel

variable (F : Funnel n)

/-- The non-sink coordinates, in index order. -/
def sources : List (Fin n) := (List.finRange n).filter fun i => F.σ i ≠ i

/-- The pushforward of a shape along a coordinate map. -/
def push (σ : Fin n → Fin n) (v : PrimeShape n) : PrimeShape n :=
  fun j => ∑ i, if σ i = j then v i else 0

/-- Mass sitting on non-sinks. -/
def sourceMass (v : PrimeShape n) : ℕ := ∑ i, if F.σ i = i then 0 else v i

end Funnel

/-- The FRACTRAN program of a funnel. -/
def funnelProg (B : PrimeBasis n) (F : Funnel n) : List ℚ :=
  F.sources.map fun i => (B.p (F.σ i) : ℚ) / B.p i

open Funnel

theorem moveUnit_add_single (v : PrimeShape n) {i : Fin n} (j : Fin n) (h : 0 < v i) :
    moveUnit v i j + Pi.single i 1 = v + Pi.single j 1 := by
  funext l
  simp only [moveUnit, Pi.add_apply, Function.update_apply, Pi.single_apply]
  split_ifs <;> subst_vars <;> omega

theorem push_add (σ : Fin n → Fin n) (v w : PrimeShape n) :
    push σ (v + w) = push σ v + push σ w := by
  funext j
  simp only [push, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp

theorem push_single (σ : Fin n → Fin n) (i : Fin n) :
    push σ (Pi.single i 1) = Pi.single (σ i) 1 := by
  funext j
  simp only [push, Pi.single_apply]
  rw [Finset.sum_eq_single i]
  · by_cases h : σ i = j
    · simp [h]
    · simp [h, Ne.symm h]
  · intro b _ hb; simp [hb]
  · simp

namespace Funnel

variable (F : Funnel n)

theorem sourceMass_add (v w : PrimeShape n) :
    F.sourceMass (v + w) = F.sourceMass v + F.sourceMass w := by
  simp only [sourceMass, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp

theorem sourceMass_single (i : Fin n) :
    F.sourceMass (Pi.single i 1) = if F.σ i = i then 0 else 1 := by
  simp only [sourceMass, Pi.single_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb; simp [hb]
  · simp

/-- Moving a unit from a source `i` to its sink `σ i` does not change the pushforward. -/
theorem push_moveUnit (v : PrimeShape n) {i : Fin n} (h : 0 < v i) :
    push F.σ (moveUnit v i (F.σ i)) = push F.σ v := by
  have e := congrArg (push F.σ) (moveUnit_add_single v (F.σ i) h)
  rw [push_add, push_add, push_single, push_single, F.idem] at e
  exact add_right_cancel e

/-- Moving a unit from a source `i` to its sink `σ i` lowers the source mass by one. -/
theorem sourceMass_moveUnit (v : PrimeShape n) {i : Fin n} (hi : F.σ i ≠ i) (h : 0 < v i) :
    F.sourceMass (moveUnit v i (F.σ i)) + 1 = F.sourceMass v := by
  have e := congrArg F.sourceMass (moveUnit_add_single v (F.σ i) h)
  rw [sourceMass_add, sourceMass_add, sourceMass_single, sourceMass_single, F.idem,
    if_neg hi, if_pos rfl] at e
  simpa using e

theorem eq_zero_of_sourceMass_eq_zero {v : PrimeShape n} (h : F.sourceMass v = 0) {i : Fin n}
    (hi : F.σ i ≠ i) : v i = 0 := by
  have := (Finset.sum_eq_zero_iff.1 h) i (Finset.mem_univ _)
  simpa [hi] using this

/-- A shape with no mass on sources is its own pushforward. -/
theorem push_eq_self {v : PrimeShape n} (h : F.sourceMass v = 0) : push F.σ v = v := by
  funext j
  simp only [push]
  rw [Finset.sum_eq_single j]
  · by_cases hj : F.σ j = j
    · simp [hj]
    · simp [hj, F.eq_zero_of_sourceMass_eq_zero h hj]
  · intro b _ hb
    by_cases hs : F.σ b = b
    · simp [hs, hb]
    · simp [F.eq_zero_of_sourceMass_eq_zero h hs]
  · simp

/-- A pushforward has no mass on sources. -/
theorem sourceMass_push (v : PrimeShape n) : F.sourceMass (push F.σ v) = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  split_ifs with hi
  · rfl
  · refine Finset.sum_eq_zero fun l _ => ?_
    split_ifs with hl
    · exact absurd (by rw [← hl, F.idem]) hi
    · rfl

theorem funnelStep (B : PrimeBasis n) (v : PrimeShape n) :
    fractranStep (funnelProg B F) (godel B v) =
      (F.sources.find? fun i => 0 < v i).map fun i => godel B (moveUnit v i (F.σ i)) :=
  fractranStep_map_godel_of_mem B F.σ v F.sources fun i hi => by
    simpa [sources] using hi

theorem find?_sources_none {v : PrimeShape n} (h : F.sourceMass v = 0) :
    F.sources.find? (fun i => 0 < v i) = none := by
  rw [List.find?_eq_none]
  intro i hi
  have : F.σ i ≠ i := by simpa [sources] using hi
  simp [F.eq_zero_of_sourceMass_eq_zero h this]

theorem find?_sources_some {v : PrimeShape n} (h : F.sourceMass v ≠ 0) :
    ∃ i, F.sources.find? (fun i => 0 < v i) = some i ∧ F.σ i ≠ i ∧ 0 < v i := by
  obtain ⟨i, hi⟩ : ∃ i, F.sources.find? (fun i => 0 < v i) = some i := by
    rw [← Option.isSome_iff_exists, List.find?_isSome]
    by_contra hc
    push_neg at hc
    refine h (Finset.sum_eq_zero fun i _ => ?_)
    split_ifs with hs
    · rfl
    · simpa using hc i (by simp [sources, hs])
  exact ⟨i, hi, by simpa [sources] using List.mem_of_find?_eq_some hi,
    by simpa using List.find?_some hi⟩

/-- **Funnel halting**: the funnel program halts on the Gödel number of any pushforward. -/
theorem funnel_halts (B : PrimeBasis n) (v : PrimeShape n) :
    fractranStep (funnelProg B F) (godel B (push F.σ v)) = none := by
  rw [funnelStep, F.find?_sources_none (F.sourceMass_push v)]; rfl

/-- **Funnel theorem**: in exactly `sourceMass v` steps, the funnel program takes the Gödel
number of `v` to the Gödel number of the pushforward `σ_* v`. -/
theorem funnel_run (B : PrimeBasis n) :
    ∀ (k : ℕ) (v : PrimeShape n), F.sourceMass v = k →
      fractranRun (funnelProg B F) k (godel B v) = some (godel B (push F.σ v))
  | 0, v, h => by rw [F.push_eq_self h]; rfl
  | k + 1, v, h => by
    obtain ⟨i, hi, hsi, hvi⟩ := F.find?_sources_some (v := v) (by omega)
    have hm := F.sourceMass_moveUnit v hsi hvi
    rw [fractranRun, funnelStep, hi, Option.map_some, Option.bind_some,
      funnel_run B k _ (by omega), F.push_moveUnit v hvi]

/-- The run cannot be extended: `sourceMass v + 1` steps fail. -/
theorem funnel_run_succ (B : PrimeBasis n) :
    ∀ (k : ℕ) (v : PrimeShape n), F.sourceMass v = k →
      fractranRun (funnelProg B F) (k + 1) (godel B v) = none
  | 0, v, h => by rw [fractranRun, funnelStep, F.find?_sources_none h]; rfl
  | k + 1, v, h => by
    obtain ⟨i, hi, hsi, hvi⟩ := F.find?_sources_some (v := v) (by omega)
    have hm := F.sourceMass_moveUnit v hsi hvi
    rw [fractranRun, funnelStep, hi, Option.map_some, Option.bind_some]
    exact funnel_run_succ B k _ (by omega)

end Funnel

/-! ### Class funnels: pushforward along `rep ∘ assign` reads off class masses -/

/-- Pushing forward along `rep ∘ a` (with `rep` injective) puts the class mass of `e` on `rep e`. -/
theorem push_classMass (a : Fin n → ShapeClass) (rep : ShapeClass → Fin n)
    (hrep : Function.Injective rep) (v : PrimeShape n) (e : ShapeClass) :
    push (rep ∘ a) v (rep e) = classMass a e v := by
  rw [classMass_eq_sum]
  simp only [push, Function.comp, hrep.eq_iff]

/-- Pushing forward along a constant map collects the total mass. -/
theorem push_const_mass (j : Fin n) (v : PrimeShape n) :
    push (fun _ => j) v j = mass v := by
  simp [push, mass_eq_sum]

end Dasein15VM.Cryptids
