import RequestProject.Dasein15VM.MonsterWalk.Tau

/-!
# McKay's 196884 (REQ-0001 item 7: `mckay_trivector`)

`mckay_trivector` states `47 · 59 · 71 + 1 = 196884` and reads `196884` as "the j-coefficient".
That reading is checked here from first principles.

* `E4 = 1 + 240 Σ σ₃(n) qⁿ` (Eisenstein series of weight 4), `Δ = q ∏ (1 - qⁿ)^24`
  (`deltaProd`, see `Tau.lean`), and `j = E4³ / Δ = q⁻¹ (c₀ + c₁ q + c₂ q² + …)`.
* Writing `J = Σ cₖ qᵏ` for `q · j`, the defining relation is `J · ∏(1 - qⁿ)^24 = E4³`; its
  coefficients up to `q²` only involve the factors `n = 1, 2`.
* `mckay_j_coefficients`: a sequence `c` satisfies this relation up to `q²` **iff**
  `c₀ = 1`, `c₁ = 744`, `c₂ = 196884`. So the coefficient of `q¹` in `j` is `196884`, and
  together with `trivector_product` this is McKay's observation `196884 = 196883 + 1`
  (`mckay_trivector_j`).
-/

open PowerSeries
namespace MonsterWalkZKP

/-- The Eisenstein series `E4 = 1 + 240 Σ σ₃(n) qⁿ`. -/
noncomputable def E4 : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 1 else 240 * (ArithmeticFunction.sigma 3 n : ℤ)

theorem E4_coeffs : coeff 0 E4 = 1 ∧ coeff 1 E4 = 240 ∧ coeff 2 E4 = 2160 := by
  refine ⟨by simp [E4], ?_, ?_⟩
  · simp [E4, ArithmeticFunction.sigma_apply]
  · simp [E4, ArithmeticFunction.sigma_apply]
    decide

theorem E4_cube_coeffs : coeff 0 (E4 ^ 3) = 1 ∧ coeff 1 (E4 ^ 3) = 720 ∧ coeff 2 (E4 ^ 3) = 179280 := by
  obtain ⟨h0, h1, h2⟩ := E4_coeffs
  have h0' : constantCoeff E4 = 1 := by rw [← coeff_zero_eq_constantCoeff_apply]; exact h0
  simp [pow_succ, coeff_mul, Finset.Nat.sum_antidiagonal_succ, h0', h1, h2]

theorem deltaProd_two_coeffs :
    coeff 0 (deltaProd 2) = 1 ∧ coeff 1 (deltaProd 2) = -24 ∧ coeff 2 (deltaProd 2) = 252 := by
  have h := (deltaList_spec 3 2 (by norm_num)).2
  have e : deltaList 3 2 = [1, -24, 252] := by decide +kernel
  rw [e] at h
  exact ⟨h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num)⟩

/-- **The first coefficients of `j`**: `q · j = 1 + 744 q + 196884 q² + ⋯`. -/
theorem mckay_j_coefficients (c : ℕ → ℤ) :
    (∀ i ≤ 2, coeff i (E4 ^ 3) = coeff i (PowerSeries.mk c * deltaProd 2)) ↔
      c 0 = 1 ∧ c 1 = 744 ∧ c 2 = 196884 := by
  obtain ⟨e0, e1, e2⟩ := E4_cube_coeffs
  obtain ⟨d0, d1, d2⟩ := deltaProd_two_coeffs
  have d0' : constantCoeff (deltaProd 2) = 1 := by rw [← coeff_zero_eq_constantCoeff_apply]; exact d0
  have k0 : coeff 0 (PowerSeries.mk c * deltaProd 2) = c 0 := by simp [d0']
  have k1 : coeff 1 (PowerSeries.mk c * deltaProd 2) = c 0 * (-24) + c 1 := by
    simp [coeff_mul, Finset.Nat.sum_antidiagonal_succ, d0', d1]
  have k2 : coeff 2 (PowerSeries.mk c * deltaProd 2) = c 0 * 252 + c 1 * (-24) + c 2 := by
    simp [coeff_mul, Finset.Nat.sum_antidiagonal_succ, d0', d1, d2]; ring
  constructor
  · intro h
    have h0 := h 0 (by norm_num); have h1 := h 1 (by norm_num); have h2 := h 2 (by norm_num)
    rw [e0, k0] at h0; rw [e1, k1] at h1; rw [e2, k2] at h2
    omega
  · rintro ⟨c0, c1, c2⟩ i hi
    interval_cases i
    · rw [e0, k0, c0]
    · rw [e1, k1, c0, c1]; norm_num
    · rw [e2, k2, c0, c1, c2]; norm_num

/-- McKay: the `q¹` coefficient of `j` is `47 · 59 · 71 + 1`. -/
theorem mckay_trivector_j (c : ℕ → ℤ)
    (h : ∀ i ≤ 2, coeff i (E4 ^ 3) = coeff i (PowerSeries.mk c * deltaProd 2)) :
    c 2 = 47 * 59 * 71 + 1 := by
  rw [((mckay_j_coefficients c).1 h).2.2]; norm_num

end MonsterWalkZKP
