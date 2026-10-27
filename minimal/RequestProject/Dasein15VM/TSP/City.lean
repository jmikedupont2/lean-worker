import RequestProject.Dasein15VM.UI.Dasein

/-!
# RFC-0004 §3.1: cities

* `carrier S`: the realizable masses of a spec — the dominant-class masses of all invariant
  states (RFC-0002 §3.4; it is `specOrders S .dominantMass`).
* `carrier_dasein`: for the Dasein15 spec, `carrier daseinSpec = {21, …, 63}` (`dasein_spectrum`).
* `carrier_subset`: every carrier is contained in `{0, …, S.mass}` (so it is finite).
* `VMSpec.withRoute`: the same spec with another dispatch table.  The carrier does not depend on
  the route (`carrier_withRoute`), so all routes share the same city set (RFC §4.2).
* `City S`: a mass of the carrier together with a realizing exponent vector.  The RFC's field
  `in_carrier` is derived (`City.in_carrier`) from the stronger field `exp_mass`: the exponent
  vector itself is a shape of the spec's conserved mass.
* `numCities S`: the number of cities (masses); `numCities_dasein : numCities daseinSpec = 43`.
* `daseinCity m`: the Dasein15 city of mass `m`, for `21 ≤ m ≤ 63`.
* `monster_off_dasein_carrier`: the Monster's home pivot `87` is not in the Dasein15 carrier.
-/

namespace Dasein15VM.TSP

open Dasein15 SpectrumVM UI

variable {n : ℕ}

/-- The carrier of a spec: the dominant-class masses of all invariant states. -/
def carrier (S : VMSpec n) : Set ℕ := specOrders S .dominantMass

/-- **The Dasein15 carrier** is `{21, …, 63}`. -/
theorem carrier_dasein : carrier daseinSpec = {m | 21 ≤ m ∧ m ≤ 63} := dasein_spectrum

theorem mem_carrier_dasein {m : ℕ} : m ∈ carrier daseinSpec ↔ 21 ≤ m ∧ m ≤ 63 := by
  rw [carrier_dasein]; rfl

/-- Every carrier mass is at most the conserved mass. -/
theorem carrier_subset (S : VMSpec n) : carrier S ⊆ {m | m ≤ S.mass} := by
  rintro m ⟨x, ⟨-, hcls, hmass⟩, rfl⟩
  show classMass S.assign x.cls x.shape ≤ S.mass
  rw [hcls, ← hmass]
  exact classMass_shapeClass_le_mass _ _

theorem carrier_finite (S : VMSpec n) : (carrier S).Finite :=
  (Set.finite_le_nat S.mass).subset (carrier_subset S)

/-- The same spec with another dispatch table. -/
def _root_.Dasein15VM.VMSpec.withRoute (S : VMSpec n) (r : ShapeClass → Fin n → Fin n) (hr : ∀ e i, r e i ≠ i) :
    VMSpec n :=
  { S with route := r, route_ne := hr }

/-- The carrier does not depend on the route. -/
theorem carrier_withRoute (S : VMSpec n) (r : ShapeClass → Fin n → Fin n)
    (hr : ∀ e i, r e i ≠ i) : carrier (S.withRoute r hr) = carrier S := rfl

/-- A city: a mass of the carrier with a realizing exponent vector. -/
structure City (S : VMSpec n) where
  mass : ℕ
  exp : PrimeShape n
  /-- The exponent vector is a shape of the conserved mass (it is realizable). -/
  exp_mass : Dasein15VM.mass exp = S.mass
  /-- The city's mass is the dominant-class mass of its exponent vector. -/
  mass_eq : mass = classMass S.assign (shapeClass S.assign exp) exp

/-- The RFC's `in_carrier` field, derived: every city lies in the carrier. -/
theorem City.in_carrier {S : VMSpec n} (c : City S) : c.mass ∈ carrier S :=
  ⟨S.ofShape c.exp 0, ⟨rfl, rfl, c.exp_mass⟩, c.mass_eq.symm⟩

/-- Every carrier mass is the mass of some city. -/
theorem exists_city {S : VMSpec n} {m : ℕ} (hm : m ∈ carrier S) : ∃ c : City S, c.mass = m := by
  obtain ⟨x, ⟨-, hcls, hmass⟩, rfl⟩ := hm
  refine ⟨⟨_, x.shape, hmass, rfl⟩, ?_⟩
  show classMass S.assign (shapeClass S.assign x.shape) x.shape = classMass S.assign x.cls x.shape
  rw [hcls]

/-- The masses of the cities are exactly the carrier. -/
theorem range_city_mass (S : VMSpec n) : Set.range (City.mass (S := S)) = carrier S := by
  ext m
  exact ⟨fun ⟨c, hc⟩ => hc ▸ c.in_carrier, fun hm => exists_city hm⟩

/-- Number of cities (distinct masses). -/
noncomputable def numCities (S : VMSpec n) : ℕ := (carrier S).ncard

theorem numCities_withRoute (S : VMSpec n) (r : ShapeClass → Fin n → Fin n)
    (hr : ∀ e i, r e i ≠ i) : numCities (S.withRoute r hr) = numCities S := rfl

/-- **The Dasein15 spec has 43 cities.** -/
theorem numCities_dasein : numCities daseinSpec = 43 := by
  rw [numCities, carrier_dasein]
  have : {m : ℕ | 21 ≤ m ∧ m ≤ 63} = Set.Icc 21 63 := rfl
  rw [this, Set.ncard_eq_toFinset_card', Set.toFinset_Icc]
  rfl

/-- The Dasein15 city of mass `m` (realized by `spectrumWitness m`). -/
def daseinCity (m : ℕ) (h : m ∈ List.range' 21 43) : City daseinSpec where
  mass := m
  exp := spectrumWitness m
  exp_mass := (spectrumWitness_spec m h).1
  mass_eq := (spectrumWitness_spec m h).2.symm

/-- **The Monster's home pivot is off the Dasein15 carrier.** -/
theorem monster_off_dasein_carrier : 87 ∉ carrier daseinSpec := by
  rw [mem_carrier_dasein]; omega

end Dasein15VM.TSP
