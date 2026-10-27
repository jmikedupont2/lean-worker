module

public import RequestProject.SpectrumVM.Exceptional

/-!
# SpectrumVM: the abstract-group / representation boundary (review §3)

Results of this library are about the matrix group `MatrixW R`.  This file proves the part of the
identification with the abstract Coxeter group `R.coxeter.Group` that is checkable by finite
computation:

* `braidCheck R = true` (kernel replay of `(s_i s_j)^{m_ij} = 1` for all `i, j`) yields a group
  homomorphism `coxeterHom` from the abstract Coxeter group onto `MatrixW R` sending simple
  reflections to simple reflections (`coxeterHom_simple`, `range_coxeterHom`);
* consequently every order in `ω(MatrixW R)` divides an element order of the abstract group;
* **faithfulness is the named boundary**: under the explicit hypothesis that `coxeterHom` is
  injective, `ω(MatrixW R)` equals the abstract spectrum (`omega_eq_abstract_of_injective`).
  Faithfulness itself is *not* proved here.

The braid relations are checked for `E₆`, `E₇` and `E₈`.
-/

@[expose] public section

namespace SpectrumVM

open Matrix

variable {n : ℕ}

/-- Kernel-replayable check of all Coxeter relations `(s_i s_j)^{m_ij} = 1`. -/
def braidCheck (R : RootDatum n) : Bool :=
  (List.finRange n).all fun i => (List.finRange n).all fun j =>
    lisOne n (lpow n (lword R [i, j]) (R.coxeter i j))

theorem isLiftable_of_braidCheck {R : RootDatum n} (h : braidCheck R = true) :
    R.coxeter.IsLiftable (reflUnit R) := by
  intro i j
  simp only [braidCheck, List.all_eq_true, List.mem_finRange, forall_const] at h
  have hij := h i j
  rw [lisOne_iff, toMat_lpow, toMat_lword] at hij
  ext1
  rw [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_one]
  simpa [wordMat] using hij

/-- The homomorphism from the abstract Coxeter group to invertible integer matrices. -/
noncomputable def coxeterHom {R : RootDatum n} (h : braidCheck R = true) :
    R.coxeter.Group →* (Matrix (Fin n) (Fin n) ℤ)ˣ :=
  R.coxeter.toCoxeterSystem.lift ⟨reflUnit R, isLiftable_of_braidCheck h⟩

theorem coxeterHom_simple {R : RootDatum n} (h : braidCheck R = true) (i : Fin n) :
    coxeterHom h (R.coxeter.simple i) = reflUnit R i := by
  have := R.coxeter.toCoxeterSystem.lift_apply_simple (isLiftable_of_braidCheck h) i
  rwa [CoxeterMatrix.toCoxeterSystem_simple] at this

/-- The image of the abstract Coxeter group is exactly `MatrixW R`. -/
theorem range_coxeterHom {R : RootDatum n} (h : braidCheck R = true) :
    (coxeterHom h).range = MatrixW R := by
  rw [MonoidHom.range_eq_map, ← R.coxeter.toCoxeterSystem.subgroup_closure_range_simple,
    MonoidHom.map_closure, MatrixW, ← Set.range_comp]
  congr 1
  ext g
  simp only [Set.mem_range, Function.comp_apply, CoxeterMatrix.toCoxeterSystem_simple]
  exact ⟨fun ⟨i, hi⟩ => ⟨i, by rw [← hi, coxeterHom_simple]⟩,
    fun ⟨i, hi⟩ => ⟨i, by rw [← hi, coxeterHom_simple]⟩⟩

/-- Every order in `ω(MatrixW R)` divides the order of some element of the abstract group. -/
theorem omega_dvd_abstract {R : RootDatum n} (h : braidCheck R = true) {m : ℕ}
    (hm : m ∈ omega R) : ∃ g : R.coxeter.Group, m ∣ orderOf g := by
  obtain ⟨x, hx, rfl⟩ := hm
  rw [← range_coxeterHom h] at hx
  obtain ⟨g, rfl⟩ := hx
  exact ⟨g, orderOf_map_dvd _ _⟩

/-- **Faithfulness boundary.** If the reflection representation is faithful (an explicit,
unproved hypothesis here), the matrix spectrum is the spectrum of the abstract Coxeter group. -/
theorem omega_eq_abstract_of_injective {R : RootDatum n} (h : braidCheck R = true)
    (hinj : Function.Injective (coxeterHom h)) :
    omega R = {m | ∃ g : R.coxeter.Group, orderOf g = m} := by
  ext m
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [← range_coxeterHom h] at hx
    obtain ⟨g, rfl⟩ := hx
    exact ⟨g, (orderOf_injective _ hinj g).symm⟩
  · rintro ⟨g, rfl⟩
    refine ⟨coxeterHom h g, ?_, orderOf_injective _ hinj g⟩
    rw [← range_coxeterHom h]; exact ⟨g, rfl⟩

theorem braidCheck_E6 : braidCheck rdE6 = true := by decide +kernel
theorem braidCheck_E7 : braidCheck rdE7 = true := by decide +kernel
theorem braidCheck_E8 : braidCheck rdE8 = true := by decide +kernel

end SpectrumVM

end
