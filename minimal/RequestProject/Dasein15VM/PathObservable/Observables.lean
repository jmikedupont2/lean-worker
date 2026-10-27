import RequestProject.Dasein15VM.PathObservable.Basic
import RequestProject.Dasein15VM.TSP.City

/-!
# Path observables, part 2: observables that read the curve

A trace `tr` is read as the discrete curve `γ t = tr[t].shape` in the exponent lattice `ℕ^n`.
Each observable below is a function `List (VMState n) → ℕ` (or `ℝ`):

* `traceLength tr`: the number of states;
* `traceSupport tr`: the number of distinct shapes visited;
* `totalVariation tr`: `Σ ‖γ (t+1) - γ t‖₁`;
* `traceWinding S tr`: the number of moves that cross the cut of the route, i.e. move a unit
  from coordinate `i` to a coordinate `< i` (for the elevator: the wrap-around `71 → 2`);
* `traceEntropy tr`: the Shannon entropy (natural log) of the visitation distribution of shapes.

Theorems:

* `totalVariation_of_chain`: along any chain of VM steps every move has `ℓ¹` length exactly `2`,
  so a certified trace has `totalVariation = 2 * (length - 1)` (`VMCorrect.totalVariation`);
* `VMCorrect.traceLength_eq`: the length is `s.steps - s₀.steps + 1` (it depends only on the
  endpoints);
* `traceSupport_le_traceLength`;
* `VMCorrect.mass_eq` and `VMCorrect.dominant_mem_carrier`: along a certified trace the total mass
  is the conserved mass and every dominant-class mass lies in the carrier;
* `traceEntropy_of_nodup`: a trace visiting pairwise distinct shapes has entropy `log length`.

`traceHilbertIndex` is **not** defined: there is no canonical Hilbert curve on `ℕ^n` for `n = 15`,
and the RFC does not fix a Hilbert pairing.
-/

namespace Dasein15VM.Path

open Dasein15VM

variable {n : ℕ} {S : VMSpec n}

/-- Number of states of a trace. -/
def traceLength (tr : List (VMState n)) : ℕ := tr.length

/-- Number of distinct shapes visited by a trace. -/
def traceSupport (tr : List (VMState n)) : ℕ := (tr.map fun x => List.ofFn x.shape).dedup.length

/-- `ℓ¹` distance between two shapes. -/
def l1 (v w : PrimeShape n) : ℕ := (List.ofFn fun i => ((v i : ℤ) - w i).natAbs).sum

theorem l1_eq_sum (v w : PrimeShape n) : l1 v w = ∑ i, ((v i : ℤ) - w i).natAbs := by
  simp [l1, List.sum_ofFn]

/-- Total variation of a trace: the sum of the `ℓ¹` lengths of its moves. -/
def totalVariation : List (VMState n) → ℕ
  | x :: y :: rest => l1 x.shape y.shape + totalVariation (y :: rest)
  | _ => 0

/-- Whether the move made from a state crosses the cut of its route. -/
def windingStep (S : VMSpec n) (x : VMState n) : ℕ :=
  match firstPos x.shape with
  | some i => if (S.route x.cls i : ℕ) < i then 1 else 0
  | none => 0

/-- Winding number of a trace: the number of moves that cross the cut. -/
def traceWinding (S : VMSpec n) (tr : List (VMState n)) : ℕ :=
  (tr.dropLast.map (windingStep S)).sum

/-- Shannon entropy (natural log) of the visitation distribution of shapes. -/
noncomputable def traceEntropy (tr : List (VMState n)) : ℝ :=
  let γ := tr.map fun x => List.ofFn x.shape
  (γ.dedup.map fun u => ((γ.count u : ℝ) / γ.length) * Real.log (γ.length / γ.count u)).sum

/-- A routed move has `ℓ¹` length `2`. -/
theorem l1_moveUnit (v : PrimeShape n) {i j : Fin n} (hij : i ≠ j) (hv : 0 < v i) :
    l1 v (moveUnit v i j) = 2 := by
  rw [l1_eq_sum]
  have : ∀ k, ((v k : ℤ) - moveUnit v i j k).natAbs =
      (if k = i then 1 else 0) + (if k = j then 1 else 0) := by
    intro k
    rw [moveUnit_int v hij hv k]
    by_cases hki : k = i
    · subst hki; simp [hij]
    · by_cases hkj : k = j
      · subst hkj; simp [Ne.symm hij]
      · simp [hki, hkj]
  simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- A VM step is a move of `ℓ¹` length `2`. -/
theorem l1_step {x y : VMState n} (h : step S x = some y) : l1 x.shape y.shape = 2 := by
  obtain ⟨v, hv, rfl, -⟩ := step_eq_some h
  unfold routeStep at hv
  obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.1 hv
  exact l1_moveUnit _ (S.route_ne _ i).symm (firstPos_spec hi)

/-- Along any chain of VM steps, the total variation is twice the number of moves. -/
theorem totalVariation_of_chain :
    ∀ (tr : List (VMState n)), (∀ i (h : i + 1 < tr.length), step S tr[i] = some tr[i + 1]) →
      totalVariation tr = 2 * (tr.length - 1)
  | [], _ => rfl
  | [_], _ => rfl
  | x :: y :: rest, h => by
    have hxy : step S x = some y := h 0 (by simp)
    have ih := totalVariation_of_chain (y :: rest)
      (fun i hi => h (i + 1) (by simp at hi ⊢; omega))
    simp only [totalVariation, l1_step hxy, ih, List.length_cons]
    omega

theorem VMCorrect.totalVariation {s₀ s : VMState n} {tr : List (VMState n)}
    (h : VMCorrect S s₀ s tr) : Path.totalVariation tr = 2 * (tr.length - 1) :=
  totalVariation_of_chain tr h.2.2.1

theorem VMCorrect.traceLength_eq {s₀ s : VMState n} {tr : List (VMState n)}
    (h : VMCorrect S s₀ s tr) : traceLength tr = s.steps - s₀.steps + 1 := h.length_eq

theorem traceSupport_le_traceLength (tr : List (VMState n)) : traceSupport tr ≤ traceLength tr :=
  (List.dedup_sublist _).length_le.trans (by simp [traceLength])

/-- Mass is conserved along a certified trace. -/
theorem VMCorrect.mass_eq {s₀ s : VMState n} {tr : List (VMState n)} (h : VMCorrect S s₀ s tr)
    {x : VMState n} (hx : x ∈ tr) : mass x.shape = S.mass := (h.2.2.2 x hx).2.2

/-- Every dominant-class mass along a certified trace lies in the carrier. -/
theorem VMCorrect.dominant_mem_carrier {s₀ s : VMState n} {tr : List (VMState n)}
    (h : VMCorrect S s₀ s tr) {x : VMState n} (hx : x ∈ tr) :
    UI.Observable.eval S .dominantMass x ∈ TSP.carrier S :=
  ⟨x, h.2.2.2 x hx, rfl⟩

/-- A trace visiting pairwise distinct shapes has entropy `log length`. -/
theorem traceEntropy_of_nodup {tr : List (VMState n)}
    (h : (tr.map fun x => List.ofFn x.shape).Nodup) : traceEntropy tr = Real.log tr.length := by
  unfold traceEntropy
  simp only
  generalize hγ : (tr.map fun x => List.ofFn x.shape) = γ at h
  have hl : γ.length = tr.length := by rw [← hγ, List.length_map]
  rw [h.dedup, ← hl]
  have : ∀ u ∈ γ, ((γ.count u : ℝ) / γ.length) * Real.log (γ.length / γ.count u) =
      (1 / γ.length) * Real.log γ.length := by
    intro u hu
    rw [List.count_eq_one_of_mem h hu]
    simp
  rw [List.map_congr_left this, List.map_const', List.sum_replicate, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos γ.length with h0 | h0
  · simp [h0]
  · field_simp

end Dasein15VM.Path
