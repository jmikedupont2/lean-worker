import RequestProject.Dasein15VM.VM

/-!
# Path observables, part 1: the structure of certified traces

Facts about `VMCorrect` traces that decide what a "path class" can be.

* `VMCorrect.steps_getElem`: the `i`-th state of a certified trace has step counter
  `s₀.steps + i`, so `VMCorrect.length_eq`: the length is `s.steps - s₀.steps + 1`.
* `VMCorrect.unique`: **a certified trace is determined by its endpoints** (the step function is
  deterministic).  Hence any rewrite relation that preserves certification and endpoints is the
  identity on certified traces: the path class of a certified trace with fixed endpoints is a
  singleton (`certified_rewrite_trivial`).
* The proposed local rewrites do not apply:
  - `step_ne_self`: no state is its own successor, so the `stutter` rewrite never fires;
  - `swap_not_step`: if `step s₁ = s₂` then `step s₂ ≠ s₁`, so `swap` destroys certification.
* `reverse_not_VMCorrect`: the reversal of a certified trace with at least two states is never
  certified (for any endpoints).
* `routeStep_not_undone`: at the level of shapes, a routed move can be undone by the next routed
  move only if the route has a 2-cycle (`τ (τ i) = i`); `elevator_no_two_cycle` shows the
  Dasein15 elevator has none, so its shape steps are never undone by one step.
-/

namespace Dasein15VM

variable {n : ℕ} {S : VMSpec n} {s₀ s : VMState n} {tr : List (VMState n)}

theorem VMCorrect.length_pos (h : VMCorrect S s₀ s tr) : 0 < tr.length := by
  rcases tr with _ | ⟨a, l⟩
  · exact absurd h.1 (by simp)
  · simp

theorem VMCorrect.getElem_zero (h : VMCorrect S s₀ s tr) : tr[0]'h.length_pos = s₀ := by
  rcases tr with _ | ⟨a, l⟩
  · exact absurd h.length_pos (by simp)
  · simpa using h.1

theorem VMCorrect.getElem_last (h : VMCorrect S s₀ s tr) :
    tr[tr.length - 1]'(by have := h.length_pos; omega) = s := by
  have h1 := h.2.1
  rw [List.getLast?_eq_getElem?] at h1
  rw [List.getElem?_eq_getElem (by have := h.length_pos; omega)] at h1
  exact Option.some.inj h1

/-- The step counter along a certified trace. -/
theorem VMCorrect.steps_getElem (h : VMCorrect S s₀ s tr) :
    ∀ i (hi : i < tr.length), tr[i].steps = s₀.steps + i
  | 0, _ => by rw [h.getElem_zero]; rfl
  | i + 1, hi => by
    rw [step_steps (h.2.2.1 i hi), h.steps_getElem i (by omega)]; rfl

/-- The length of a certified trace is determined by its endpoints. -/
theorem VMCorrect.length_eq (h : VMCorrect S s₀ s tr) : tr.length = s.steps - s₀.steps + 1 := by
  have := h.steps_getElem (tr.length - 1) (by have := h.length_pos; omega)
  rw [h.getElem_last] at this
  have := h.length_pos
  omega

/-- Two certified traces from the same start agree position by position. -/
theorem VMCorrect.getElem_eq {s' : VMState n} {tr' : List (VMState n)}
    (h : VMCorrect S s₀ s tr) (h' : VMCorrect S s₀ s' tr') :
    ∀ i (hi : i < tr.length) (hi' : i < tr'.length), tr[i] = tr'[i]
  | 0, _, _ => by rw [h.getElem_zero, h'.getElem_zero]
  | i + 1, hi, hi' => by
    have e1 := h.2.2.1 i hi
    have e2 := h'.2.2.1 i hi'
    rw [VMCorrect.getElem_eq h h' i (by omega) (by omega), e2] at e1
    exact (Option.some.inj e1).symm

/-- **Certified traces are determined by their endpoints.** -/
theorem VMCorrect.unique {tr' : List (VMState n)} (h : VMCorrect S s₀ s tr)
    (h' : VMCorrect S s₀ s tr') : tr = tr' := by
  have hl : tr.length = tr'.length := by rw [h.length_eq, h'.length_eq]
  exact List.ext_getElem hl fun i hi hi' => h.getElem_eq h' i hi hi'

/-- Any relation that preserves certification with fixed endpoints is trivial on certified
traces: the path class of a certified trace (endpoints fixed) is a singleton. -/
theorem certified_rewrite_trivial (R : List (VMState n) → List (VMState n) → Prop)
    (hR : ∀ {a b}, R a b → VMCorrect S s₀ s a → VMCorrect S s₀ s b) {a b : List (VMState n)}
    (hab : Relation.ReflTransGen R a b) (ha : VMCorrect S s₀ s a) : a = b := by
  induction hab with
  | refl => rfl
  | tail _ hbc ih =>
    subst ih
    exact ha.unique (hR hbc ha)

/-- No state is its own successor (the `stutter` rewrite never fires). -/
theorem step_ne_self (S : VMSpec n) (x : VMState n) : step S x ≠ some x := by
  intro h
  have := step_steps h
  omega

/-- Two consecutive steps can never be swapped. -/
theorem swap_not_step {x y : VMState n} (h : step S x = some y) : step S y ≠ some x := by
  intro h'
  have := step_steps h
  have := step_steps h'
  omega

/-- The reversal of a certified trace with at least two states is not certified. -/
theorem reverse_not_VMCorrect (h : VMCorrect S s₀ s tr) (hl : 2 ≤ tr.length)
    (a b : VMState n) : ¬ VMCorrect S a b tr.reverse := by
  intro hr
  have e := hr.2.2.1 0 (by simp; omega)
  have h1 := step_steps e
  simp only [List.getElem_reverse] at h1
  rw [h.steps_getElem _ (by omega), h.steps_getElem _ (by omega)] at h1
  omega

/-! ### Shape-level reversibility depends on the route -/

theorem firstPos_spec {v : PrimeShape n} {i : Fin n} (h : firstPos v = some i) : 0 < v i := by
  have := List.find?_some h
  simpa using this

theorem moveUnit_int (v : PrimeShape n) {i j : Fin n} (hij : i ≠ j) (hv : 0 < v i) (k : Fin n) :
    (moveUnit v i j k : ℤ) = v k - (if k = i then 1 else 0) + (if k = j then 1 else 0) := by
  unfold moveUnit
  by_cases hkj : k = j
  · subst hkj; simp [Ne.symm hij]
  · by_cases hki : k = i
    · subst hki; simp [hkj]; omega
    · simp [hkj, hki]

/-- A routed move undone by the next routed move forces a 2-cycle of the route. -/
theorem routeStep_not_undone {τ : Fin n → Fin n} (hτ : ∀ i, τ i ≠ i) {v w : PrimeShape n}
    (h1 : routeStep τ v = some w) (h2 : routeStep τ w = some v) : ∃ i, τ (τ i) = i := by
  unfold routeStep at h1 h2
  obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.1 h1
  obtain ⟨j, hj, hv⟩ := Option.map_eq_some_iff.1 h2
  have hvi := firstPos_spec hi
  have hwj := firstPos_spec hj
  have key : ∀ k, (v k : ℤ) = v k - (if k = i then 1 else 0) + (if k = τ i then 1 else 0)
      - (if k = j then 1 else 0) + (if k = τ j then 1 else 0) := by
    intro k
    have h3 : ((moveUnit (moveUnit v i (τ i)) j (τ j) k : ℕ) : ℤ) = v k := by rw [congrFun hv k]
    rw [moveUnit_int _ (hτ j).symm hwj, moveUnit_int _ (hτ i).symm hvi] at h3
    linarith
  have hti := hτ i
  have htj := hτ j
  have ka := key (τ i)
  have kb := key (τ j)
  refine ⟨i, ?_⟩
  by_cases hja : j = τ i
  · subst hja
    by_cases hb : τ (τ i) = i
    · exact hb
    · simp [hb] at kb
  · simp [hti, Ne.symm hja] at ka
    split_ifs at ka <;> omega

/-- The Dasein15 elevator has no 2-cycle. -/
theorem elevator_no_two_cycle : ∀ i, elevator (elevator i) ≠ i := by decide

/-- Elevator shape steps are never undone by the next step. -/
theorem elevator_step_not_undone {v w : PrimeShape 15} (h1 : routeStep elevator v = some w) :
    routeStep elevator w ≠ some v := fun h2 =>
  let ⟨i, hi⟩ := routeStep_not_undone elevator_ne h1 h2
  elevator_no_two_cycle i hi

end Dasein15VM
