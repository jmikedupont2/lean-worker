import Mathlib

/-!
# Dasein15 VM: real Clifford algebras `Cl(p,q)`

The 8-periodic quantity in `Dasein15VM/NormMod8.lean` is a residue of a number, not a K-theory
class. This file works with the actual objects: real Clifford algebras, built from Mathlib's
`CliffordAlgebra` (convention `ι v * ι v = Q v`).

* `Cl p q`: the Clifford algebra of `ℝ^{p+q}` with `Q v = v₁² + … + v_p² − v_{p+1}² − … − v_{p+q}²`.
* `signFlipEquiv`: for a diagonal form with `w i₀ = ±1`, the generators
  `e_{i₀} ↦ e_{i₀}`, `eᵢ ↦ eᵢ e_{i₀}` give an algebra isomorphism `Cl(w) ≅ Cl(w')` with
  `w' i = −wᵢ w_{i₀}` (`i ≠ i₀`). Both directions are built with `CliffordAlgebra.lift` and the
  two composites are checked to be the identity on generators.
* `clSwapEquiv p q : Cl (p+1) q ≃ₐ[ℝ] Cl (q+1) p` — the classical identity
  `Cl(p,q) ≅ Cl(q+1, p−1)`.
* `cl96_equiv_cl78 : Cl 9 6 ≃ₐ[ℝ] Cl 7 8`, and hence
  `bott_iff_claim_false_nat` / `bott_iff_claim_false_int`: the statement
  "for `p+q = p'+q' = 15`, `Cl(p,q) ≅ Cl(p',q')` **iff** `p − q ≡ p' − q' (mod 8)`" is false
  (with `ℕ` subtraction as written, and also with integer subtraction). `9 − 6 = 3` and
  `7 − 8 = −1` differ mod 8, but the algebras are isomorphic.

What is true classically (not formalized here): for fixed `p + q`, `p − q ≡ p' − q' (mod 8)`
implies `Cl(p,q) ≅ Cl(p',q')`; the converse fails in odd dimension, where two residues give the
same complex matrix algebra (for `n = 15`, residues 3 and 7 in this convention).
For Dasein15's assignment, "Earth primes square to `+1`, Spoke/Hub primes to `−1`" is the
signature `(7, 8)`: `Cl 7 8` is the algebra in `cl96_equiv_cl78`.
-/

namespace Dasein15VM.KTheory

open CliffordAlgebra

variable {K : Type*} [Fintype K] [DecidableEq K]

/-- The diagonal quadratic form `∑ wᵢ vᵢ²`. -/
noncomputable abbrev Qw (w : K → ℝ) : QuadraticForm ℝ (K → ℝ) := QuadraticMap.weightedSumSquares ℝ w

/-- Projection killing the coordinate `i₀`. -/
noncomputable def killAt (i₀ : K) : (K → ℝ) →ₗ[ℝ] (K → ℝ) :=
  LinearMap.id - (LinearMap.proj i₀).smulRight (Pi.single i₀ 1)

omit [Fintype K] in
theorem killAt_apply (i₀ : K) (v : K → ℝ) (i : K) :
    killAt i₀ v i = if i = i₀ then 0 else v i := by
  by_cases h : i = i₀
  · subst h; simp [killAt]
  · simp [killAt, h]

theorem polar_killAt_single (w : K → ℝ) (i₀ : K) (v : K → ℝ) :
    QuadraticMap.polar (Qw w) (killAt i₀ v) (Pi.single i₀ 1) = 0 := by
  simp only [QuadraticMap.polar, QuadraticMap.weightedSumSquares_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases h : i = i₀
  · subst h; simp [killAt_apply]
  · simp [killAt_apply, h]

theorem Qw_single (w : K → ℝ) (i₀ : K) : Qw w (Pi.single i₀ 1) = w i₀ := by
  rw [QuadraticMap.weightedSumSquares_apply, Finset.sum_eq_single i₀]
  · simp
  · intro b _ hb; simp [hb]
  · simp

theorem Qw_split (w : K → ℝ) (i₀ : K) (v : K → ℝ) :
    Qw w v = w i₀ * (v i₀ * v i₀) + Qw w (killAt i₀ v) := by
  have : Qw w v - Qw w (killAt i₀ v) = w i₀ * (v i₀ * v i₀) := by
    simp only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul]
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i₀]
    · simp [killAt_apply]
    · intro b _ hb; simp [killAt_apply, hb]
    · simp
  linarith

/-- The sign-flip map on generators: `e_{i₀} ↦ e_{i₀}`, `eᵢ ↦ c · eᵢ e_{i₀}` (`i ≠ i₀`). -/
noncomputable def flipLin (w' : K → ℝ) (i₀ : K) (c : ℝ) :
    (K → ℝ) →ₗ[ℝ] CliffordAlgebra (Qw w') :=
  (ι (Qw w')).comp ((LinearMap.proj i₀).smulRight (Pi.single i₀ 1)) +
    c • (LinearMap.mulRight ℝ (ι (Qw w') (Pi.single i₀ 1))).comp ((ι (Qw w')).comp (killAt i₀))

theorem flipLin_apply (w' : K → ℝ) (i₀ : K) (c : ℝ) (v : K → ℝ) :
    flipLin w' i₀ c v = v i₀ • ι (Qw w') (Pi.single i₀ 1) +
      c • (ι (Qw w') (killAt i₀ v) * ι (Qw w') (Pi.single i₀ 1)) := by
  simp [flipLin]

theorem sq_aux_clifford {A : Type*} [Ring A] [Algebra ℝ A] (x y : A) (a c qx qy : ℝ)
    (hyx : y * x = -(x * y)) (hyy : y * y = algebraMap ℝ A qy) (hxx : x * x = algebraMap ℝ A qx) :
    (a • y + c • (x * y)) * (a • y + c • (x * y)) =
      algebraMap ℝ A (a * a * qy - c * c * (qx * qy)) := by
  have e1 : y * (x * y) = -(x * y * y) := by rw [← mul_assoc, hyx, neg_mul]
  have e2 : x * y * (x * y) = -(x * x * (y * y)) := by
    rw [show x * y * (x * y) = x * (y * x) * y by noncomm_ring, hyx]; noncomm_ring
  rw [add_mul, mul_add, mul_add, smul_mul_smul_comm, smul_mul_smul_comm, smul_mul_smul_comm,
    smul_mul_smul_comm, e1, e2, mul_assoc x y y, hyy, hxx]
  simp only [Algebra.smul_def, ← map_mul, mul_neg, ← map_neg]
  rw [mul_comm c a, sub_eq_add_neg, map_add]; abel

theorem flipLin_sq (w w' : K → ℝ) (i₀ : K) (c : ℝ) (hc : c * c = 1) (h0 : w' i₀ = w i₀)
    (hw : ∀ i, i ≠ i₀ → w i = -(w' i * w' i₀)) (v : K → ℝ) :
    flipLin w' i₀ c v * flipLin w' i₀ c v = algebraMap ℝ _ (Qw w v) := by
  have hyx : ι (Qw w') (Pi.single i₀ 1) * ι (Qw w') (killAt i₀ v) =
      -(ι (Qw w') (killAt i₀ v) * ι (Qw w') (Pi.single i₀ 1)) := by
    have := ι_mul_ι_add_swap (Q := Qw w') (killAt i₀ v) (Pi.single i₀ 1)
    rw [polar_killAt_single, map_zero] at this
    exact (neg_eq_of_add_eq_zero_right this).symm
  have hyy : ι (Qw w') (Pi.single i₀ 1) * ι (Qw w') (Pi.single i₀ 1) =
      algebraMap ℝ _ (w' i₀) := by rw [ι_sq_scalar, Qw_single]
  have hQ : Qw w v = v i₀ * v i₀ * w' i₀ - c * c * (Qw w' (killAt i₀ v) * w' i₀) := by
    rw [Qw_split w i₀, h0, hc, one_mul]
    simp only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul, Finset.sum_mul]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    have : ∑ i, w i * (killAt i₀ v i * killAt i₀ v i) =
        ∑ i, -(w' i * (killAt i₀ v i * killAt i₀ v i) * w i₀) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h : i = i₀
      · subst h; simp [killAt_apply]
      · rw [hw i h, h0]; ring
    rw [this]; ring
  rw [flipLin_apply, hQ]
  exact sq_aux_clifford _ _ _ _ _ _ hyx hyy (ι_sq_scalar _ _)

/-- The sign-flip algebra map `Cl(w) → Cl(w')`. -/
noncomputable def flipHom (w w' : K → ℝ) (i₀ : K) (c : ℝ) (hc : c * c = 1) (h0 : w' i₀ = w i₀)
    (hw : ∀ i, i ≠ i₀ → w i = -(w' i * w' i₀)) :
    CliffordAlgebra (Qw w) →ₐ[ℝ] CliffordAlgebra (Qw w') :=
  lift (Qw w) ⟨flipLin w' i₀ c, flipLin_sq w w' i₀ c hc h0 hw⟩

theorem flipHom_ι (w w' : K → ℝ) (i₀ : K) (c : ℝ) (hc : c * c = 1) (h0 : w' i₀ = w i₀)
    (hw : ∀ i, i ≠ i₀ → w i = -(w' i * w' i₀)) (v : K → ℝ) :
    flipHom w w' i₀ c hc h0 hw (ι (Qw w) v) = flipLin w' i₀ c v :=
  lift_ι_apply _ _ _

omit [Fintype K] in
theorem killAt_single (i₀ : K) : killAt i₀ (Pi.single i₀ 1) = 0 := by
  funext i; by_cases h : i = i₀ <;> simp [killAt_apply, h]

omit [Fintype K] in
theorem killAt_killAt (i₀ : K) (v : K → ℝ) : killAt i₀ (killAt i₀ v) = killAt i₀ v := by
  funext i; by_cases h : i = i₀ <;> simp [killAt_apply, h]

omit [Fintype K] in
theorem killAt_add (i₀ : K) (v : K → ℝ) : v i₀ • (Pi.single i₀ 1 : K → ℝ) + killAt i₀ v = v := by
  funext i; by_cases h : i = i₀
  · subst h; simp [killAt_apply]
  · simp [killAt_apply, h]

/-- Composing two sign flips with `c * c' * w i₀ = 1` gives the identity. -/
theorem flipHom_comp (w w' : K → ℝ) (i₀ : K) (c c' : ℝ) (hc : c * c = 1) (hc' : c' * c' = 1)
    (h0 : w' i₀ = w i₀) (hw : ∀ i, i ≠ i₀ → w i = -(w' i * w' i₀))
    (hw' : ∀ i, i ≠ i₀ → w' i = -(w i * w i₀)) (hcc : c * c' * w i₀ = 1) :
    (flipHom w' w i₀ c' hc' h0.symm hw').comp (flipHom w w' i₀ c hc h0 hw) = AlgHom.id ℝ _ := by
  refine hom_ext (LinearMap.ext fun v => ?_)
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply, flipHom_ι,
    AlgHom.id_apply, flipLin_apply, map_add, map_smul, map_mul]
  have hk : killAt i₀ v i₀ = 0 := by simp [killAt_apply]
  simp only [Pi.single_eq_same, one_smul, killAt_single, map_zero, zero_mul, smul_zero, add_zero,
    killAt_killAt, hk, zero_smul, zero_add]
  rw [smul_mul_assoc, mul_assoc, ι_sq_scalar, Qw_single, ← Algebra.commutes, ← Algebra.smul_def,
    smul_smul, smul_smul, hcc, one_smul, ← map_smul, ← map_add,
    killAt_add]

/-- The sign-flipped weights: `w' i₀ = w i₀`, `w' i = -(w i * w i₀)` for `i ≠ i₀`. -/
noncomputable def flipW (w : K → ℝ) (i₀ : K) : K → ℝ := fun i => if i = i₀ then w i₀ else -(w i * w i₀)

/-- **Sign-flip isomorphism.** If `w i₀ = ±1`, then `Cl(w) ≅ Cl(flipW w i₀)` as `ℝ`-algebras. -/
noncomputable def signFlipEquiv (w : K → ℝ) (i₀ : K) (h : w i₀ * w i₀ = 1) :
    CliffordAlgebra (Qw w) ≃ₐ[ℝ] CliffordAlgebra (Qw (flipW w i₀)) :=
  have h0 : flipW w i₀ i₀ = w i₀ := by simp [flipW]
  have hw' : ∀ i, i ≠ i₀ → flipW w i₀ i = -(w i * w i₀) := fun i hi => by simp [flipW, hi]
  have hw : ∀ i, i ≠ i₀ → w i = -(flipW w i₀ i * flipW w i₀ i₀) := fun i hi => by
    rw [hw' i hi, h0]
    linear_combination (-(w i)) * h
  AlgEquiv.ofAlgHom (flipHom w (flipW w i₀) i₀ 1 (one_mul 1) h0 hw)
    (flipHom (flipW w i₀) w i₀ (w i₀) h h0.symm hw')
    (flipHom_comp (flipW w i₀) w i₀ (w i₀) 1 h (one_mul 1) h0.symm hw' hw
      (by rw [h0, mul_one, h]))
    (flipHom_comp w (flipW w i₀) i₀ 1 (w i₀) (one_mul 1) h h0 hw hw' (by rw [one_mul, h]))

/-- Reindexing the coordinates is an isometry of diagonal forms. -/
noncomputable def reindexIso {K' : Type*} [Fintype K'] (e : K ≃ K') (w : K' → ℝ) :
    QuadraticMap.IsometryEquiv (Qw w) (Qw (w ∘ e)) where
  toLinearEquiv := LinearEquiv.funCongrLeft ℝ ℝ e
  map_app' v := by
    simp only [QuadraticMap.weightedSumSquares_apply, Function.comp]
    exact Equiv.sum_comp e (fun i => w i • (v i * v i))

/-! ### `Cl(p,q)` -/

/-- Signature weights: the first `p` coordinates square to `+1`, the last `q` to `-1`. -/
noncomputable def sig (p q : ℕ) : Fin (p + q) → ℝ := fun i => if (i : ℕ) < p then 1 else -1

/-- The real Clifford algebra `Cl(p,q)` of `ℝ^{p+q}` with `v² = v₁² + … + v_p² - … - v_{p+q}²`
(Mathlib's `CliffordAlgebra` convention `ι v * ι v = Q v`). -/
abbrev Cl (p q : ℕ) := CliffordAlgebra (Qw (sig p q))

/-- `0 ↦ 0`, `1..p ↦ q+1..q+p`, `p+1..p+q ↦ 1..q`. -/
def swapFun (p q : ℕ) (i : Fin (p + 1 + q)) : Fin (q + 1 + p) :=
  ⟨if (i : ℕ) = 0 then 0 else if (i : ℕ) ≤ p then i + q else i - p, by split_ifs <;> omega⟩

/-- The reindexing `Fin (p+1+q) ≃ Fin (q+1+p)` used by `clSwapEquiv`. -/
def swapPerm (p q : ℕ) : Fin (p + 1 + q) ≃ Fin (q + 1 + p) where
  toFun := swapFun p q
  invFun := swapFun q p
  left_inv i := by
    apply Fin.ext; simp only [swapFun]; split_ifs <;> omega
  right_inv j := by
    apply Fin.ext; simp only [swapFun]; split_ifs <;> omega

theorem flipW_sig (p q : ℕ) :
    flipW (sig (p + 1) q) 0 = sig (q + 1) p ∘ swapPerm p q := by
  funext i
  simp only [flipW, sig, swapPerm, Function.comp, Equiv.coe_fn_mk, swapFun, Fin.ext_iff,
    Fin.val_zero]
  split_ifs <;> first | omega | norm_num

/-- **`Cl(p+1, q) ≅ Cl(q+1, p)`** for all `p q` (the classical identity `Cl(p,q) ≅ Cl(q+1,p-1)`). -/
noncomputable def clSwapEquiv (p q : ℕ) : Cl (p + 1) q ≃ₐ[ℝ] Cl (q + 1) p :=
  (signFlipEquiv (sig (p + 1) q) 0 (by simp [sig])).trans
    ((AlgEquiv.cast (by rw [flipW_sig])).trans
      (CliffordAlgebra.equivOfIsometry (reindexIso (swapPerm p q) (sig (q + 1) p))).symm)

/-- **`Cl(9,6) ≅ Cl(7,8)`** as real algebras (`clSwapEquiv 8 6`). -/
noncomputable def cl96_equiv_cl78 : Cl 9 6 ≃ₐ[ℝ] Cl 7 8 := clSwapEquiv 8 6

/-- **The proposed "real Bott periodicity" iff is false** (with `ℕ` subtraction, as written):
`Cl(9,6) ≅ Cl(7,8)` but `9 - 6 = 3` and `7 - 8 = 0` are not congruent mod 8. -/
theorem bott_iff_claim_false_nat :
    ¬ ∀ p q p' q' : ℕ, p + q = 15 → p' + q' = 15 →
      ((p - q ≡ p' - q' [MOD 8]) ↔ Nonempty (Cl p q ≃ₐ[ℝ] Cl p' q')) := by
  intro h
  have := (h 9 6 7 8 rfl rfl).2 ⟨cl96_equiv_cl78⟩
  revert this; decide

/-- **The same iff is false with integer subtraction**: `3 ≢ -1 (mod 8)`. -/
theorem bott_iff_claim_false_int :
    ¬ ∀ p q p' q' : ℕ, p + q = 15 → p' + q' = 15 →
      (((p : ℤ) - q ≡ (p' : ℤ) - q' [ZMOD 8]) ↔ Nonempty (Cl p q ≃ₐ[ℝ] Cl p' q')) := by
  intro h
  have := (h 9 6 7 8 rfl rfl).2 ⟨cl96_equiv_cl78⟩
  revert this; decide

end Dasein15VM.KTheory
