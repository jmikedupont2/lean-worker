import RequestProject.Dasein15

/-!
# Dasein15 VM, phase 1: prime shapes and shape classes

Generalizes `Dasein15.sspExp` / `Dasein15.eigenspace` / `Dasein15.eigenMass` from the fixed
15 supersingular primes to an arbitrary finite basis of distinct primes.

* `PrimeBasis n`: `n` distinct primes (`Dasein15.SSP` is the instance `sspBasis`).
* `PrimeShape n`: an exponent vector; `shapeOf B c` is the exponent vector of `c` over `B`
  (`shapeOf sspBasis = Dasein15.sspExp` by `rfl`), `godel B v` is the Gödel number
  `∏ i, B.p i ^ v i`, and `shapeOf_godel` shows `shapeOf B (godel B v) = v`.
* `ShapeClass` is `Dasein15.Eigenspace`; a class assignment `a : Fin n → ShapeClass` gives
  `classMass a e v` (`classMass Dasein15.eigenspace = Dasein15.eigenMass`) and the class of a
  shape, `shapeClass a v`: the class of maximal mass, ties broken Earth > Spoke > Hub > Clock.
-/

namespace Dasein15VM

open Dasein15

/-- A basis of `n` distinct primes. -/
structure PrimeBasis (n : ℕ) where
  p : Fin n → ℕ
  prime : ∀ i, (p i).Prime
  injective : Function.Injective p

/-- An exponent vector over a prime basis. -/
abbrev PrimeShape (n : ℕ) := Fin n → ℕ

/-- The shape classes: Dasein15's four eigenspaces. -/
abbrev ShapeClass := Dasein15.Eigenspace

variable {n : ℕ}

/-- The exponent vector of `c` over the basis `B` (generalizes `Dasein15.sspExp`). -/
noncomputable def shapeOf (B : PrimeBasis n) (c : ℕ) : PrimeShape n :=
  fun i => c.factorization (B.p i)

/-- The Gödel number of a shape (kernel-computable list product). -/
def godel (B : PrimeBasis n) (v : PrimeShape n) : ℕ :=
  (List.ofFn fun i => B.p i ^ v i).prod

/-- Total mass of a shape (kernel-computable list sum). -/
def mass (v : PrimeShape n) : ℕ := (List.ofFn v).sum

/-- Mass carried by the class `e` under the assignment `a` (generalizes `Dasein15.eigenMass`). -/
def classMass (a : Fin n → ShapeClass) (e : ShapeClass) (v : PrimeShape n) : ℕ :=
  (List.ofFn fun i => if a i = e then v i else 0).sum

/-- The (dominant) class of a shape: maximal class mass, ties broken Earth > Spoke > Hub > Clock. -/
def shapeClass (a : Fin n → ShapeClass) (v : PrimeShape n) : ShapeClass :=
  if classMass a .Spoke v ≤ classMass a .Earth v ∧ classMass a .Hub v ≤ classMass a .Earth v ∧
      classMass a .Clock v ≤ classMass a .Earth v then .Earth
  else if classMass a .Hub v ≤ classMass a .Spoke v ∧
      classMass a .Clock v ≤ classMass a .Spoke v then .Spoke
  else if classMass a .Clock v ≤ classMass a .Hub v then .Hub
  else .Clock

theorem godel_eq_prod (B : PrimeBasis n) (v : PrimeShape n) :
    godel B v = ∏ i, B.p i ^ v i := by
  simp [godel, List.prod_ofFn]

theorem mass_eq_sum (v : PrimeShape n) : mass v = ∑ i, v i := by
  simp [mass, List.sum_ofFn]

theorem classMass_eq_sum (a : Fin n → ShapeClass) (e : ShapeClass) (v : PrimeShape n) :
    classMass a e v = ∑ i, if a i = e then v i else 0 := by
  simp [classMass, List.sum_ofFn]

/-- `shapeClass` picks a class of maximal mass. -/
theorem classMass_le_shapeClass (a : Fin n → ShapeClass) (v : PrimeShape n) (e : ShapeClass) :
    classMass a e v ≤ classMass a (shapeClass a v) v := by
  unfold shapeClass
  cases e <;> split_ifs <;> omega

theorem godel_pos (B : PrimeBasis n) (v : PrimeShape n) : 0 < godel B v := by
  rw [godel_eq_prod]
  exact Finset.prod_pos fun i _ => pow_pos (B.prime i).pos _

theorem godel_ne_zero (B : PrimeBasis n) (v : PrimeShape n) : godel B v ≠ 0 :=
  (godel_pos B v).ne'

/-- The exponent vector of a Gödel number is the shape it encodes. -/
theorem shapeOf_godel (B : PrimeBasis n) (v : PrimeShape n) : shapeOf B (godel B v) = v := by
  funext i
  rw [shapeOf, godel_eq_prod, Nat.factorization_prod fun j _ => pow_ne_zero _ (B.prime j).ne_zero]
  rw [Finsupp.finset_sum_apply, Finset.sum_eq_single i]
  · simp [(B.prime i).factorization_pow]
  · intro j _ hji
    simp [(B.prime j).factorization_pow, B.injective.ne hji]
  · simp

/-- A basis prime divides a Gödel number iff its exponent is positive. -/
theorem dvd_godel_iff (B : PrimeBasis n) (v : PrimeShape n) (i : Fin n) :
    B.p i ∣ godel B v ↔ 0 < v i := by
  constructor
  · intro h
    have := (B.prime i).factorization_pos_of_dvd (godel_ne_zero B v) h
    have e := congrFun (shapeOf_godel B v) i
    simp only [shapeOf] at e
    omega
  · intro h
    rw [godel_eq_prod]
    exact (dvd_pow_self _ h.ne').trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))

/-- The 15 supersingular primes as a prime basis. -/
def sspBasis : PrimeBasis 15 where
  p := SSP
  prime := SSP_all_prime
  injective := by decide

theorem shapeOf_sspBasis : shapeOf sspBasis = sspExp := rfl

theorem classMass_dasein (e : ShapeClass) (v : PrimeShape 15) :
    classMass eigenspace e v = eigenMass e v := by
  rw [classMass_eq_sum]; rfl

theorem mass_dasein (v : PrimeShape 15) : mass v = totalMass v := by
  rw [mass_eq_sum]; rfl

/-- On unit shapes, `shapeClass` recovers Dasein15's per-prime eigenspace: the class of the
shape of the prime `SSP i` is `eigenspace i`. -/
theorem shapeClass_sspExp_prime (i : Fin 15) :
    shapeClass eigenspace (sspExp (SSP i)) = eigenspace i := by
  have : sspExp (SSP i) = Pi.single i 1 := by
    funext j
    simp only [sspExp, (SSP_all_prime i).factorization, Finsupp.single_apply, Pi.single_apply]
    by_cases h : j = i
    · subst h; simp
    · have : SSP i ≠ SSP j := fun e => h (sspBasis.injective e.symm)
      simp [h, this]
  rw [this]
  clear this
  revert i; decide

end Dasein15VM
