import RequestProject.Dasein15VM.Fractran

/-!
# Dasein15 VM, phase 5: exponent-up / exponent-down transitions

`growGen i` multiplies the configuration by the basis prime `p i` (one more unit of mass at
`i`); `shrinkGen i` divides by `p i` when possible.  Both are exact on Gödel numbers and change
the mass by exactly one; `moveUnit` (the routed step) is a shrink followed by a grow, which is why
it conserves mass.
-/

namespace Dasein15VM

variable {n : ℕ}

/-- Add one unit of mass at `i`. -/
def growGen (i : Fin n) (v : PrimeShape n) : PrimeShape n := Function.update v i (v i + 1)

/-- Remove one unit of mass at `i` (if present). -/
def shrinkGen (i : Fin n) (v : PrimeShape n) : Option (PrimeShape n) :=
  if 0 < v i then some (Function.update v i (v i - 1)) else none

theorem godel_growGen (B : PrimeBasis n) (i : Fin n) (v : PrimeShape n) :
    godel B (growGen i v) = godel B v * B.p i := by
  have k := prod_update_mul B v i (v i + 1)
  rw [godel_eq_prod, godel_eq_prod, growGen]
  rw [pow_succ, ← mul_assoc] at k
  exact Nat.eq_of_mul_eq_mul_right (pow_pos (B.prime i).pos (v i)) (by rw [k]; ring)

theorem mass_growGen (i : Fin n) (v : PrimeShape n) : mass (growGen i v) = mass v + 1 := by
  have k := sum_update_add v i (v i + 1)
  rw [mass_eq_sum, mass_eq_sum, growGen]
  omega

theorem shrinkGen_isSome_iff (B : PrimeBasis n) (i : Fin n) (v : PrimeShape n) :
    (shrinkGen i v).isSome ↔ B.p i ∣ godel B v := by
  rw [dvd_godel_iff, shrinkGen]
  split_ifs with h <;> simp [h]

theorem godel_shrinkGen (B : PrimeBasis n) {i : Fin n} {v w : PrimeShape n}
    (h : shrinkGen i v = some w) : godel B w * B.p i = godel B v := by
  unfold shrinkGen at h
  split_ifs at h with hv
  cases h
  have e : growGen i (Function.update v i (v i - 1)) = v := by
    funext j
    by_cases hj : j = i
    · subst hj; simp [growGen]; omega
    · simp [growGen, hj]
  rw [← godel_growGen, e]

theorem mass_shrinkGen {i : Fin n} {v w : PrimeShape n} (h : shrinkGen i v = some w) :
    mass w + 1 = mass v := by
  unfold shrinkGen at h
  split_ifs at h with hv
  cases h
  have k := sum_update_add v i (v i - 1)
  rw [mass_eq_sum, mass_eq_sum]
  omega

theorem shrinkGen_growGen (i : Fin n) (v : PrimeShape n) :
    shrinkGen i (growGen i v) = some v := by
  simp [shrinkGen, growGen]

/-- The routed move is shrink-then-grow. -/
theorem moveUnit_eq (v : PrimeShape n) (i j : Fin n) (h : 0 < v i) :
    shrinkGen i v = some (Function.update v i (v i - 1)) ∧
      moveUnit v i j = growGen j (Function.update v i (v i - 1)) := by
  simp [shrinkGen, h, moveUnit, growGen]

end Dasein15VM
