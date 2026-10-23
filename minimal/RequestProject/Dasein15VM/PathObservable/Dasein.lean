import RequestProject.Dasein15VM.PathObservable.Graph
import RequestProject.Dasein15VM.Walk

/-!
# Path observables, part 4: the Dasein15 walk as a path

* `dasein_certified`: the 500-state walk is a certified trace (from `dasein_VMCorrect`).
* `dasein_pathClass`: its path class is that of its start state `s₀` (`PathEquiv` with `[s₀]`).
* Observables, kernel-computed: `traceLength = 500`, `traceSupport = 500` (all 500 shapes are
  distinct), `totalVariation = 998` (also from the general theorem), `traceWinding = 0` (no unit
  crosses `71 → 2` in 499 steps), and `traceEntropy = log 500`.
* Direction: `dasein_reverse_not_certified` (the reversed trace is not certified) and
  `dasein_shape_step_not_undone` (no elevator shape step is undone by the next one) — the Dasein15
  path is directed.
* `dasein_traceLength_not_descends`: `traceLength` is not a path-class invariant for this spec.
* `dasein_misses_city_21`: the walk never visits dominant mass `21`, so it is not a tour of the
  43-mass carrier (the superseded RFC-0004 v1 criterion `daseinTour : SoundTour` cannot hold).
-/

namespace Dasein15VM.Path

open Dasein15VM Dasein15

theorem dasein_certified : Certified daseinSpec daseinTrace :=
  certified_iff.2 ⟨_, _, dasein_VMCorrect⟩

theorem daseinTrace_head? : daseinTrace.head? = some s₀ := dasein_VMCorrect.1

theorem s₀_invariant : VMInvariant daseinSpec s₀ := dasein_VMCorrect.2.2.2 s₀ (by
  have := daseinTrace_head?
  exact List.mem_of_mem_head? this)

/-- The path class of the Dasein15 walk is the class of its start state. -/
theorem dasein_pathClass : PathEquiv daseinSpec daseinTrace [s₀] := by
  rw [pathEquiv_iff_head dasein_certified (certified_singleton_iff.2 s₀_invariant)]
  exact daseinTrace_head?

theorem dasein_traceLength : traceLength daseinTrace = 500 := daseinTrace_length

set_option maxRecDepth 100000 in
theorem dasein_traceSupport : traceSupport daseinTrace = 500 := by decide +kernel

theorem dasein_totalVariation : totalVariation daseinTrace = 998 := by
  rw [VMCorrect.totalVariation dasein_VMCorrect, daseinTrace_length]

set_option maxRecDepth 100000 in
theorem dasein_traceWinding : traceWinding daseinSpec daseinTrace = 0 := by decide +kernel

set_option maxRecDepth 100000 in
theorem dasein_shapes_nodup : (daseinTrace.map fun x => List.ofFn x.shape).Nodup := by
  decide +kernel

theorem dasein_traceEntropy : traceEntropy daseinTrace = Real.log 500 := by
  rw [traceEntropy_of_nodup dasein_shapes_nodup, daseinTrace_length]; norm_num

/-- The reversed Dasein15 walk is not certified. -/
theorem dasein_reverse_not_certified : ¬ Certified daseinSpec daseinTrace.reverse := by
  rw [certified_iff]
  rintro ⟨a, b, h⟩
  exact reverse_not_VMCorrect dasein_VMCorrect (by rw [daseinTrace_length]; omega) a b h

/-- No shape step of the Dasein15 spec is undone by the next step. -/
theorem dasein_shape_step_not_undone {e e' : ShapeClass} {v w : PrimeShape 15}
    (h : routeStep (daseinSpec.route e) v = some w) : routeStep (daseinSpec.route e') w ≠ some v :=
  elevator_step_not_undone h

/-- `traceLength` is not a path-class invariant for the Dasein15 spec. -/
theorem dasein_traceLength_not_descends : ¬ Descends daseinSpec traceLength := by
  obtain ⟨b, hb⟩ := extend_exists (certified_singleton_iff.2 s₀_invariant) (by decide)
  exact traceLength_not_descends hb

set_option maxRecDepth 100000 in
/-- The walk never visits dominant mass `21`. -/
theorem dasein_misses_city_21 :
    ∀ x ∈ daseinTrace, UI.Observable.eval daseinSpec .dominantMass x ≠ 21 := by
  decide +kernel

theorem dasein_not_tour :
    ¬ ∀ m ∈ TSP.carrier daseinSpec,
      ∃ x ∈ daseinTrace, UI.Observable.eval daseinSpec .dominantMass x = m := fun h => by
  obtain ⟨x, hx, h21⟩ := h 21 (TSP.mem_carrier_dasein.2 (by omega))
  exact dasein_misses_city_21 x hx h21

end Dasein15VM.Path
