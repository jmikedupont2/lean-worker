import RequestProject.Dasein15VM.TSP.City
import RequestProject.Dasein15VM.TSP.Dist
import RequestProject.Dasein15VM.TSP.Tour

/-!
# RFC-0004 v1 (cities and directed spectral cost) — superseded by the path-observable revision

* `TSP.City`: `carrier`, `City`, `numCities_dasein = 43`, `monster_off_dasein_carrier`.
* `TSP.Dist`: `pivot_exists`, `spectralDist` (via `Nat.find`), its closed form, the asymmetry
  witness `21 → 42` vs `42 → 21`, and `rfc_pivot_exists_false` (common multiples in the carrier
  need not exist).
* `TSP.Tour`: `rfc_tour_empty` (the v1 `Tour` conditions are contradictory for 43 cities).

The revised RFC-0004 lives in `RequestProject.Dasein15VM.PathObservable`.
-/
