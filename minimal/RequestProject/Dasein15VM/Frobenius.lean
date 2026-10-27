import RequestProject.Dasein15VM.Shape

/-!
# Dasein15 VM: Frobenius fixed-field retraction and the field-graded layer

For a finite field `K` (`#K = q`) and a finite extension `L`:
* `frob_fixed_iff`: `x ^ q = x ↔ x ∈ range (algebraMap K L)` — the fixed field of the Frobenius
  `x ↦ x ^ q` is exactly `K`; `extension_frob_fixed_iff` states it for Mathlib's
  `FiniteField.Extension.frob`.
* `frob_bijective`: `x ↦ x ^ q` is a bijection of `L` — its *image* is all of `L`, so the
  retraction content is the fixed field, not the image (`gf27_frob_not_into_prime_field`).
* `frobRetract`: the partial fixed-field retraction `L → Option K`, with
  `frobRetract_algebraMap` (shrink ∘ grow = id), `frobRetract_isSome_iff`, and
  `frobRetract_exists_none` (it is genuinely partial when `L ≠ K`).
* Trace: `trace_surjective` (always), `traceRetract_algebraMap` (`[L:K]⁻¹ • trace` retracts when
  `[L:K]` is invertible in `K`), `trace_algebraMap_eq_zero` (trace kills `K` when `p ∣ [L:K]`).
  The explicit formula `Tr(x) = Σ_{i<[L:K]} x^(q^i)` is Mathlib's
  `FiniteField.algebraMap_trace_eq_sum_pow`.
* Tower `GF(p^a) ⊆ GF(p^(ab))`: embeddings exist, the fixed field of `x ↦ x^(p^a)` is the image
  of any embedding, and `towerRetract` satisfies the retraction law.
* `FieldLayer` / `FieldInstr` (`extendField`, `frobRetract`): the field-graded layer; the
  specialized object at grade `d` is `GF(p^d)`, with `#GF(p^d) = p^d` equal to the Gödel number
  of the pure prime-power shape (`card_galoisField_eq_godel`).
-/

namespace Dasein15VM.Frobenius

open Polynomial

section General

variable {K L : Type*} [Field K] [Finite K] [Field L] [Algebra K L]

theorem algebraMap_pow_card (a : K) : (algebraMap K L a) ^ Nat.card K = algebraMap K L a := by
  haveI := Fintype.ofFinite K
  rw [← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]

theorem frob_fixed_iff [Finite L] (x : L) :
    x ^ Nat.card K = x ↔ x ∈ Set.range (algebraMap K L) := by
  classical
  haveI := Fintype.ofFinite K
  constructor
  · intro hx
    have hq : 1 < Nat.card K := Finite.one_lt_card
    have hq' : 1 < Fintype.card K := by rwa [Nat.card_eq_fintype_card] at hq
    set P : L[X] := X ^ Nat.card K - X
    have hdeg : P.natDegree = Nat.card K := by
      simp only [P]; rw [natDegree_sub_eq_left_of_natDegree_lt] <;> simp; omega
    have hP0 : P ≠ 0 := by
      intro h; rw [h, natDegree_zero] at hdeg; omega
    have hroot : ∀ y : L, y ∈ P.roots.toFinset ↔ y ^ Nat.card K = y := by
      intro y
      rw [Multiset.mem_toFinset, mem_roots hP0]
      simp [P, sub_eq_zero]
    set T := (Finset.univ : Finset K).image (algebraMap K L)
    have hT : T ⊆ P.roots.toFinset := by
      intro y hy
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hy
      exact (hroot _).2 (algebraMap_pow_card a)
    have hcard : P.roots.toFinset.card ≤ T.card := by
      rw [Finset.card_image_of_injective _ (algebraMap K L).injective, Finset.card_univ,
        ← Nat.card_eq_fintype_card, ← hdeg]
      exact (Multiset.toFinset_card_le _).trans (card_roots' P)
    have := Finset.eq_of_subset_of_card_le hT hcard
    have hx' : x ∈ T := this ▸ (hroot x).2 hx
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hx'
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact algebraMap_pow_card a

theorem frob_bijective [Finite L] : Function.Bijective (fun x : L => x ^ Nat.card K) := by
  haveI := Fintype.ofFinite K
  have := (FiniteField.frobeniusAlgEquivOfAlgebraic K L).bijective
  convert this using 1
  funext x
  simp [Nat.card_eq_fintype_card]

/-- The relative Frobenius `Extension.frob` fixes exactly the base field. -/
theorem extension_frob_fixed_iff (k : Type*) [Field k] [Finite k] (p : ℕ) [Fact p.Prime]
    [CharP k p] (n : ℕ) [NeZero n] (x : FiniteField.Extension k p n) :
    FiniteField.Extension.frob k p n x = x ↔
      x ∈ Set.range (algebraMap k (FiniteField.Extension k p n)) := by
  rw [FiniteField.Extension.frob_apply]
  exact frob_fixed_iff x

open Classical in
/-- Frobenius fixed-field retraction (partial): a fixed point of `x ↦ x ^ #K` is sent to its
preimage in `K`; other elements are rejected. -/
noncomputable def frobRetract [Finite L] (x : L) : Option K :=
  if h : x ^ Nat.card K = x then some ((frob_fixed_iff x).1 h).choose else none

theorem frobRetract_algebraMap [Finite L] (a : K) :
    frobRetract (K := K) (algebraMap K L a) = some a := by
  have h := algebraMap_pow_card (L := L) a
  rw [frobRetract, dif_pos h]
  congr 1
  exact (algebraMap K L).injective ((frob_fixed_iff _).1 h).choose_spec

theorem frobRetract_eq_some [Finite L] {x : L} {a : K} (h : frobRetract x = some a) :
    algebraMap K L a = x := by
  unfold frobRetract at h
  split_ifs at h with hx
  cases h
  exact ((frob_fixed_iff x).1 hx).choose_spec

theorem frobRetract_isSome_iff [Finite L] (x : L) :
    (frobRetract (K := K) x).isSome ↔ x ^ Nat.card K = x := by
  unfold frobRetract
  split_ifs with hx <;> simp [hx]

/-- If `L` is strictly bigger than `K`, the retraction is genuinely partial. -/
theorem frobRetract_exists_none [Finite L] (h : Nat.card K < Nat.card L) :
    ∃ x : L, frobRetract (K := K) x = none := by
  by_contra hall
  push_neg at hall
  have hsurj : Function.Surjective (algebraMap K L) := by
    intro x
    obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 (hall x)
    exact ⟨a, frobRetract_eq_some ha⟩
  exact absurd (Nat.card_le_card_of_surjective _ hsurj) (by omega)

/-- The trace is a surjective `K`-linear map `L → K`. -/
theorem trace_surjective [Finite L] : Function.Surjective (Algebra.trace K L) := by
  haveI : FiniteDimensional K L := Module.Finite.of_finite
  exact Algebra.trace_surjective K L

omit [Finite K] in
theorem trace_algebraMap (a : K) [Finite L] :
    Algebra.trace K L (algebraMap K L a) = (Module.finrank K L : K) * a := by
  haveI : FiniteDimensional K L := Module.Finite.of_finite
  rw [Algebra.trace_algebraMap, nsmul_eq_mul]

/-- When the degree is invertible in `K`, `(degree)⁻¹ • trace` is a `K`-linear retraction. -/
noncomputable def traceRetract : L →ₗ[K] K := (Module.finrank K L : K)⁻¹ • Algebra.trace K L

omit [Finite K] in
theorem traceRetract_algebraMap [Finite L] (h : (Module.finrank K L : K) ≠ 0) (a : K) :
    traceRetract (algebraMap K L a) = a := by
  rw [traceRetract, LinearMap.smul_apply, trace_algebraMap, smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ h, one_mul]

omit [Finite K] in
/-- When the characteristic divides the degree, the trace kills the base field, so the
trace cannot be rescaled into a retraction. -/
theorem trace_algebraMap_eq_zero [Finite L] (h : (Module.finrank K L : K) = 0) (a : K) :
    Algebra.trace K L (algebraMap K L a) = 0 := by
  rw [trace_algebraMap, h, zero_mul]

end General

/-! ## The tower `GF(p^a) ⊆ GF(p^(a b))` -/

section Tower

variable (p : ℕ) [Fact p.Prime]

theorem galoisField_embedding_exists {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Nonempty (GaloisField p a →ₐ[ZMod p] GaloisField p (a * b)) :=
  FiniteField.nonempty_algHom_of_finrank_dvd (by
    rw [GaloisField.finrank p ha, GaloisField.finrank p (mul_ne_zero ha hb)]
    exact dvd_mul_right a b)

/-- Fixed field of `x ↦ x ^ (p ^ a)` on `GF(p^(a b))` is the image of `GF(p^a)`, for any
embedding. -/
theorem galoisField_tower_fixed_iff {a b : ℕ} (ha : a ≠ 0)
    (φ : GaloisField p a →ₐ[ZMod p] GaloisField p (a * b)) (x : GaloisField p (a * b)) :
    x ^ (p ^ a) = x ↔ x ∈ Set.range φ := by
  letI : Algebra (GaloisField p a) (GaloisField p (a * b)) := φ.toRingHom.toAlgebra
  have := frob_fixed_iff (K := GaloisField p a) x
  rwa [GaloisField.card p a ha] at this

/-- The shrink map of the tower: Frobenius fixed-field retraction along `φ`. -/
noncomputable def towerRetract {a b : ℕ} (φ : GaloisField p a →ₐ[ZMod p] GaloisField p (a * b))
    (x : GaloisField p (a * b)) : Option (GaloisField p a) :=
  letI : Algebra (GaloisField p a) (GaloisField p (a * b)) := φ.toRingHom.toAlgebra
  frobRetract x

/-- Retraction law: shrinking after growing is the identity. -/
theorem towerRetract_grow {a b : ℕ} (φ : GaloisField p a →ₐ[ZMod p] GaloisField p (a * b))
    (y : GaloisField p a) : towerRetract p φ (φ y) = some y := by
  letI : Algebra (GaloisField p a) (GaloisField p (a * b)) := φ.toRingHom.toAlgebra
  exact frobRetract_algebraMap y

theorem towerRetract_isSome_iff {a b : ℕ} (ha : a ≠ 0)
    (φ : GaloisField p a →ₐ[ZMod p] GaloisField p (a * b)) (x : GaloisField p (a * b)) :
    (towerRetract p φ x).isSome ↔ x ^ (p ^ a) = x := by
  letI : Algebra (GaloisField p a) (GaloisField p (a * b)) := φ.toRingHom.toAlgebra
  have := frobRetract_isSome_iff (K := GaloisField p a) x
  rwa [GaloisField.card p a ha] at this

theorem towerRetract_eq_some {a b : ℕ} (φ : GaloisField p a →ₐ[ZMod p] GaloisField p (a * b))
    {x : GaloisField p (a * b)} {y : GaloisField p a} (h : towerRetract p φ x = some y) :
    φ y = x := by
  letI : Algebra (GaloisField p a) (GaloisField p (a * b)) := φ.toRingHom.toAlgebra
  exact frobRetract_eq_some h

/-- For `b > 1` the shrink is genuinely partial: growing after shrinking is not total. -/
theorem towerRetract_exists_none {a b : ℕ} (ha : a ≠ 0) (hb : 1 < b)
    (φ : GaloisField p a →ₐ[ZMod p] GaloisField p (a * b)) :
    ∃ x, towerRetract p φ x = none := by
  letI : Algebra (GaloisField p a) (GaloisField p (a * b)) := φ.toRingHom.toAlgebra
  apply frobRetract_exists_none
  rw [GaloisField.card p a ha, GaloisField.card p _ (mul_ne_zero ha (by omega))]
  exact Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (by nlinarith [Nat.pos_of_ne_zero ha])

end Tower

/-! ## `GF(27)` over `GF(3)` -/

section GF27

instance fact_prime_three' : Fact (Nat.Prime 3) := ⟨by norm_num⟩

theorem gf27_finrank : Module.finrank (ZMod 3) (GaloisField 3 3) = 3 :=
  GaloisField.finrank 3 (by norm_num)

theorem gf27_card : Nat.card (GaloisField 3 3) = 27 := GaloisField.card 3 3 (by norm_num)

/-- In `GF(27)`, `x ^ 3 = x` exactly on the prime field `GF(3)`. -/
theorem gf27_fixed_iff (x : GaloisField 3 3) :
    x ^ 3 = x ↔ x ∈ Set.range (algebraMap (ZMod 3) (GaloisField 3 3)) := by
  have := frob_fixed_iff (K := ZMod 3) x
  rwa [Nat.card_zmod] at this

/-- `x ↦ x ^ 3` does **not** map `GF(27)` into `GF(3)`: it is a bijection of `GF(27)`. -/
theorem gf27_frob_not_into_prime_field :
    ¬ ∀ x : GaloisField 3 3, x ^ 3 ∈ Set.range (algebraMap (ZMod 3) (GaloisField 3 3)) := by
  intro h
  have hb := frob_bijective (K := ZMod 3) (L := GaloisField 3 3)
  simp only [Nat.card_zmod] at hb
  have hsurj : Function.Surjective (algebraMap (ZMod 3) (GaloisField 3 3)) := by
    intro y
    obtain ⟨x, rfl⟩ := hb.2 y
    exact h x
  have := Nat.card_le_card_of_surjective _ hsurj
  rw [gf27_card, Nat.card_zmod] at this
  omega

end GF27

/-! ## Field layers: the specialized object of a pure prime-power shape -/

/-- A field layer: prime `p`, grade `d > 0`; its specialized object is `GF(p^d)`. -/
structure FieldLayer where
  p : ℕ
  [hp : Fact p.Prime]
  d : ℕ
  hd : d ≠ 0

attribute [instance] FieldLayer.hp

/-- The specialized object of a layer. -/
abbrev FieldLayer.Carrier (L : FieldLayer) : Type := GaloisField L.p L.d

/-- Layer instructions. -/
inductive FieldInstr
  /-- Grow: pass to the degree-`b` extension. -/
  | extendField (b : ℕ)
  /-- Shrink: retract onto the subfield of degree `a`. -/
  | frobRetract (a : ℕ)

/-- Execute an instruction on a layer (grade arithmetic is along divisibility). -/
def FieldLayer.exec : FieldInstr → FieldLayer → Option FieldLayer
  | .extendField b, L => if hb : b = 0 then none else
      some { p := L.p, hp := L.hp, d := L.d * b, hd := mul_ne_zero L.hd hb }
  | .frobRetract a, L => if h : a ≠ 0 ∧ a ∣ L.d then
      some { p := L.p, hp := L.hp, d := a, hd := h.1 } else none

theorem FieldLayer.card_carrier (L : FieldLayer) : Nat.card L.Carrier = L.p ^ L.d :=
  GaloisField.card L.p L.d L.hd

/-- Grade-level retraction law: shrinking back after growing returns the original layer. -/
theorem FieldLayer.retract_extend (L : FieldLayer) {b : ℕ} (hb : b ≠ 0) :
    ((L.exec (.extendField b)).bind (FieldLayer.exec (.frobRetract L.d))) = some L := by
  simp [FieldLayer.exec, hb, L.hd]

/-- Every shrink step `d ↦ a` comes with an embedding `GF(p^a) → GF(p^d)` (writing `d = a b`)
whose image is exactly the fixed field of `x ↦ x ^ (p ^ a)`. -/
theorem FieldLayer.exec_retract_embedding (L L' : FieldLayer) (a : ℕ)
    (h : L.exec (.frobRetract a) = some L') :
    L'.p = L.p ∧ L'.d = a ∧ ∃ b, L.d = a * b ∧
      ∃ φ : GaloisField L.p a →ₐ[ZMod L.p] GaloisField L.p (a * b),
        ∀ x, x ^ (L.p ^ a) = x ↔ x ∈ Set.range φ := by
  simp only [FieldLayer.exec] at h
  split_ifs at h with ha
  cases h
  obtain ⟨b, hb⟩ := ha.2
  have hb0 : b ≠ 0 := by rintro rfl; exact L.hd (by simpa using hb)
  obtain ⟨φ⟩ := galoisField_embedding_exists L.p ha.1 hb0
  exact ⟨rfl, rfl, b, hb, φ, galoisField_tower_fixed_iff L.p ha.1 φ⟩

/-- The specialized object at the pure prime-power configuration `p_i ^ d` has exactly that many
elements: `#GF(p_i^d) = godel B (d • e_i)`. -/
theorem card_galoisField_eq_godel {n : ℕ} (B : PrimeBasis n) (i : Fin n) {d : ℕ} (hd : d ≠ 0) :
    haveI := Fact.mk (B.prime i)
    Nat.card (GaloisField (B.p i) d) = godel B (Pi.single i d) := by
  haveI := Fact.mk (B.prime i)
  rw [GaloisField.card _ _ hd, godel_eq_prod, Finset.prod_eq_single i]
  · simp
  · intro j _ hj; simp [hj]
  · simp

end Dasein15VM.Frobenius
