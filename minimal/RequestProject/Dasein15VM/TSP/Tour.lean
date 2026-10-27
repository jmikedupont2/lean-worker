import RequestProject.Dasein15VM.TSP.Dist

/-!
# RFC-0004 (v1, superseded) §3.3: the `Tour` structure is empty

The v1 `Tour` asked for `cities.Nodup`, `cities.length = numCities S` and
`cities.head? = cities.getLast?`.  A duplicate-free list whose first and last entries agree has at
most one element (`length_le_one_of_nodup_head_eq_last`), so for the Dasein15 spec (43 cities)
the v1 `Tour` type has no inhabitant (`rfc_tour_empty`).  This is recorded as a gap in the
superseded v1 text; the revised RFC-0004 replaces tours by path classes
(`RequestProject.Dasein15VM.PathObservable`).
-/

namespace Dasein15VM.TSP

theorem length_le_one_of_nodup_head_eq_last {α : Type} :
    ∀ {l : List α}, l.Nodup → l.head? = l.getLast? → l.length ≤ 1
  | [], _, _ => by simp
  | [_], _, _ => by simp
  | a :: b :: rest, hnd, he => by
    exfalso
    rw [List.getLast?_cons_cons, List.head?_cons, List.getLast?_eq_some_getLast (by simp)] at he
    have hmem : (b :: rest).getLast (by simp) ∈ b :: rest := List.getLast_mem _
    rw [← Option.some.inj he] at hmem
    exact (List.nodup_cons.1 hnd).1 hmem

/-- The v1 `Tour` conditions cannot hold for the 43 Dasein15 cities. -/
theorem rfc_tour_empty (cities : List (City daseinSpec)) (hnd : cities.Nodup)
    (hlen : cities.length = numCities daseinSpec) (hclosed : cities.head? = cities.getLast?) :
    False := by
  have := length_le_one_of_nodup_head_eq_last hnd hclosed
  rw [hlen, numCities_dasein] at this
  omega

end Dasein15VM.TSP
