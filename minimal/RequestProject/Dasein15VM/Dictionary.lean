import RequestProject.Dasein15VM.Ingest
import RequestProject.Dasein15VM.Transitions
import RequestProject.Dasein15VM.Frobenius

/-!
# Dictionary: the Dasein15 VM vocabulary in standard mathematics

Each section identifies a construction of the VM with a standard object and proves the
identification.

1. **Gödel numbering = unique factorization.** `godel B` is a monoid homomorphism from
   `(PrimeShape n, +)` to `(ℕ, *)` (`godelHom`), injective (`godel_injective`). Divisibility is the
   pointwise order (`godel_dvd_godel_iff`), `gcd` is pointwise `min` (`godel_inf`), `lcm` is
   pointwise `max` (`godel_sup`).
2. **Mass = big Omega.** `mass v` is the number of prime factors with multiplicity of the Gödel
   number: `cardFactors (godel B v) = mass v` (`cardFactors_godel`).
3. **`growGen` / `shrinkGen` = counter increment / guarded decrement.** `growGen i v = v + eᵢ`
   (`growGen_eq_add_single`), and `shrinkGen i` is exactly the partial inverse of `growGen i`
   (`isPartialInv_growGen`). These are the two instructions of a Minsky register machine.
4. **`moveUnit` = moving one chip.** `moveUnit v i j + eᵢ = v + eⱼ` when `vᵢ > 0`
   (`moveUnit_add_single`): one chip goes from site `i` to site `j`, so mass (chip count) is
   conserved. The FRACTRAN fraction `p j / p i` is the vector `eⱼ - eᵢ`.
5. **`frobRetract` = the same partial inverse, one level up.** `frobRetract` is the partial inverse
   of the field embedding `algebraMap K L` (`isPartialInv_frobRetract`). So `shrinkGen`/`growGen`
   and `frobRetract`/`algebraMap` are both instances of `Function.IsPartialInv`.
6. **Shape classes = push-forward along a colouring, then argmax.** The four class masses add up to
   the total mass (`sum_classMass`), i.e. `classMass a · v` is the push-forward of `v` along
   `a : Fin n → ShapeClass`, and `shapeClass` picks a class of maximal mass.
7. **Trace checking = `List.IsChain` + reflection.** `checkChain S l = true` iff `l` is a chain
   for the relation "`b` is the VM successor of `a`" (`checkChain_iff_isChain`); together with
   `checkVMTrace_iff` this is the standard proof-by-reflection pattern for a decidable predicate.
-/

namespace Dasein15VM

open SpectrumVM

variable {n : ℕ}

/-! ### 1. Gödel numbering is unique factorization -/

theorem godel_zero (B : PrimeBasis n) : godel B 0 = 1 := by
  simp [godel_eq_prod]

theorem godel_add (B : PrimeBasis n) (v w : PrimeShape n) :
    godel B (v + w) = godel B v * godel B w := by
  simp [godel_eq_prod, pow_add, Finset.prod_mul_distrib]

/-- `godel B` as a monoid homomorphism `(PrimeShape n, +) → (ℕ, *)`. -/
def godelHom (B : PrimeBasis n) : Multiplicative (PrimeShape n) →* ℕ where
  toFun v := godel B v.toAdd
  map_one' := godel_zero B
  map_mul' v w := godel_add B v.toAdd w.toAdd

theorem godel_injective (B : PrimeBasis n) : Function.Injective (godel B) := fun v w h => by
  rw [← shapeOf_godel B v, h, shapeOf_godel]

/-- The factorization of a Gödel number vanishes at primes outside the basis. -/
theorem factorization_godel_of_ne (B : PrimeBasis n) (v : PrimeShape n) {q : ℕ}
    (hq : ∀ i, B.p i ≠ q) : (godel B v).factorization q = 0 := by
  rw [godel_eq_prod, Nat.factorization_prod fun j _ => pow_ne_zero _ (B.prime j).ne_zero,
    Finsupp.finset_sum_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  simp [(B.prime j).factorization_pow, hq j]

theorem factorization_godel_basis (B : PrimeBasis n) (v : PrimeShape n) (i : Fin n) :
    (godel B v).factorization (B.p i) = v i :=
  congrFun (shapeOf_godel B v) i

/-- **Divisibility is the pointwise order.** -/
theorem godel_dvd_godel_iff (B : PrimeBasis n) (v w : PrimeShape n) :
    godel B v ∣ godel B w ↔ v ≤ w := by
  rw [← Nat.factorization_le_iff_dvd (godel_ne_zero B v) (godel_ne_zero B w)]
  constructor
  · intro h i
    have := h (B.p i)
    rwa [factorization_godel_basis, factorization_godel_basis] at this
  · intro h q
    by_cases hq : ∃ i, B.p i = q
    · obtain ⟨i, rfl⟩ := hq
      rw [factorization_godel_basis, factorization_godel_basis]; exact h i
    · push_neg at hq
      rw [factorization_godel_of_ne B v hq]; exact Nat.zero_le _

/-- **`gcd` is pointwise `min`.** -/
theorem godel_inf (B : PrimeBasis n) (v w : PrimeShape n) :
    godel B (v ⊓ w) = Nat.gcd (godel B v) (godel B w) := by
  apply Nat.eq_of_factorization_eq (godel_ne_zero B _)
    (Nat.gcd_ne_zero_left (godel_ne_zero B v))
  intro q
  rw [Nat.factorization_gcd (godel_ne_zero B v) (godel_ne_zero B w)]
  by_cases hq : ∃ i, B.p i = q
  · obtain ⟨i, rfl⟩ := hq
    simp only [Finsupp.inf_apply, factorization_godel_basis, Pi.inf_apply]
  · push_neg at hq
    simp [factorization_godel_of_ne B _ hq]

/-- **`lcm` is pointwise `max`.** -/
theorem godel_sup (B : PrimeBasis n) (v w : PrimeShape n) :
    godel B (v ⊔ w) = Nat.lcm (godel B v) (godel B w) := by
  apply Nat.eq_of_factorization_eq (godel_ne_zero B _)
    (Nat.lcm_ne_zero (godel_ne_zero B v) (godel_ne_zero B w))
  intro q
  rw [Nat.factorization_lcm (godel_ne_zero B v) (godel_ne_zero B w)]
  by_cases hq : ∃ i, B.p i = q
  · obtain ⟨i, rfl⟩ := hq
    simp only [Finsupp.sup_apply, factorization_godel_basis, Pi.sup_apply]
  · push_neg at hq
    simp [factorization_godel_of_ne B _ hq]

/-! ### 2. Mass is big Omega -/

theorem cardFactors_prod_pow (B : PrimeBasis n) (v : PrimeShape n) (s : Finset (Fin n)) :
    ArithmeticFunction.cardFactors (∏ i ∈ s, B.p i ^ v i) = ∑ i ∈ s, v i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      ArithmeticFunction.cardFactors_mul (pow_ne_zero _ (B.prime a).ne_zero)
        (Finset.prod_ne_zero_iff.2 fun j _ => pow_ne_zero _ (B.prime j).ne_zero),
      ArithmeticFunction.cardFactors_apply_prime_pow (B.prime a), ih]

/-- **Mass is the number of prime factors counted with multiplicity** (`Ω`). -/
theorem cardFactors_godel (B : PrimeBasis n) (v : PrimeShape n) :
    ArithmeticFunction.cardFactors (godel B v) = mass v := by
  rw [godel_eq_prod, mass_eq_sum, cardFactors_prod_pow]

/-! ### 3. `growGen` / `shrinkGen`: increment and guarded decrement -/

theorem growGen_eq_add_single (i : Fin n) (v : PrimeShape n) :
    growGen i v = v + Pi.single i 1 := by
  funext j
  by_cases h : j = i
  · subst h; simp [growGen]
  · simp [growGen, h]

/-- `shrinkGen i` is the partial inverse of `growGen i`. -/
theorem isPartialInv_growGen (i : Fin n) : Function.IsPartialInv (growGen i) (shrinkGen i) := by
  intro x y
  constructor
  · intro h
    unfold shrinkGen at h
    split_ifs at h with hy
    cases h
    funext j
    by_cases hj : j = i
    · subst hj; simp [growGen]; omega
    · simp [growGen, hj]
  · rintro rfl; exact shrinkGen_growGen i x

/-! ### 4. `moveUnit` moves one chip -/

theorem moveUnit_add_single (v : PrimeShape n) {i : Fin n} (j : Fin n) (h : 0 < v i) :
    moveUnit v i j + Pi.single i 1 = v + Pi.single j 1 := by
  obtain ⟨-, hm⟩ := moveUnit_eq v i j h
  rw [hm, growGen_eq_add_single, add_assoc, add_comm (Pi.single j 1), ← add_assoc]
  congr 1
  rw [← growGen_eq_add_single]
  funext k
  by_cases hk : k = i
  · subst hk; simp [growGen]; omega
  · simp [growGen, hk]

/-! ### 5. `frobRetract` is the partial inverse of the field embedding -/

theorem isPartialInv_frobRetract {K L : Type*} [Field K] [Finite K] [Field L] [Algebra K L]
    [Finite L] : Function.IsPartialInv (algebraMap K L) (Frobenius.frobRetract (K := K)) := by
  intro a x
  constructor
  · exact Frobenius.frobRetract_eq_some
  · rintro rfl; exact Frobenius.frobRetract_algebraMap a

/-! ### 6. Shape classes are a push-forward along a colouring -/

theorem sum_classMass (a : Fin n → ShapeClass) (v : PrimeShape n) :
    classMass a .Earth v + classMass a .Spoke v + classMass a .Hub v + classMass a .Clock v =
      mass v := by
  simp only [classMass_eq_sum, mass_eq_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  cases a i <;> simp

/-! ### 7. Trace checking is `List.IsChain` -/

theorem checkChain_iff_isChain (S : VMSpec n) :
    ∀ l : List (VMState n), checkChain S l = true ↔ List.IsChain (fun a b => step S a = some b) l
  | [] => by simp [checkChain]
  | [_] => by simp [checkChain]
  | s :: t :: rest => by
    rw [List.isChain_cons_cons, ← checkChain_iff_isChain S (t :: rest), ← checkStep_iff]
    simp [checkChain]

end Dasein15VM
