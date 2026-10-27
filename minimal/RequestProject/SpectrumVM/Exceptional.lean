module

public import RequestProject.SpectrumVM.Closure
public import RequestProject.SpectrumVM.Comparison

/-!
# SpectrumVM: the exceptional root data `E₆`, `E₇`, `E₈`

Root data are built from Mathlib's `CoxeterMatrix.E₆/E₇/E₈` (never re-typed).  All facts below are
kernel-established through the order-certificate replay (`decide +kernel`, no `native_decide`):

* known values: Coxeter elements have orders 12, 18, 30, and in `E₇` the 9th power of a Coxeter
  element is `-1`;
* `2ρ` (the solution of `C x = 2·1`) derived from the Mathlib Cartan matrices;
* **lower bounds** for the golden spectra: every golden order of `W(E₆)`, `W(E₇)`, `W(E₈)` occurs
  (witnesses for the maximal orders, plus K4);
* the comparison engine reproduces `E₆ ⊆ E₇ ⊆ E₈` for the witnessed order ideals, with covering
  pairs.

**Not established here:** completeness (upper bounds) of these spectra.  Those remain the open
gating items M1/M2/M4; see `STATUS.md`.
-/

@[expose] public section

namespace SpectrumVM

open Matrix

def rdE6 : RootDatum 6 := RootDatum.ofCoxeter CoxeterMatrix.E₆ (by decide)
def rdE7 : RootDatum 7 := RootDatum.ofCoxeter CoxeterMatrix.E₇ (by decide)
def rdE8 : RootDatum 8 := RootDatum.ofCoxeter CoxeterMatrix.E₈ (by decide)

/-! ### Known values (RFC §12) -/

theorem E6_coxeter_order : orderOf (wordMat rdE6 [0, 1, 2, 3, 4, 5]) = 12 :=
  checkOrderCert_sound (c := ⟨[0, 1, 2, 3, 4, 5], ⟨[(2, 2), (3, 1)], 12⟩⟩) (by decide +kernel)

theorem E7_coxeter_order : orderOf (wordMat rdE7 [0, 1, 2, 3, 4, 5, 6]) = 18 :=
  checkOrderCert_sound (c := ⟨[0, 1, 2, 3, 4, 5, 6], ⟨[(2, 1), (3, 2)], 18⟩⟩)
    (by decide +kernel)

theorem E8_coxeter_order : orderOf (wordMat rdE8 [0, 1, 2, 3, 4, 5, 6, 7]) = 30 :=
  checkOrderCert_sound (c := ⟨[0, 1, 2, 3, 4, 5, 6, 7], ⟨[(2, 1), (3, 1), (5, 1)], 30⟩⟩)
    (by decide +kernel)

/-- In `E₇` the 9th power of a Coxeter element is `-1`. -/
theorem E7_coxeter_pow_nine : wordMat rdE7 [0, 1, 2, 3, 4, 5, 6] ^ 9 = -1 := by
  have h : lisEq 7 (lpow 7 (lword rdE7 [0, 1, 2, 3, 4, 5, 6]) 9)
      (ltab 7 fun i j => if i = j then -1 else 0) = true := by decide +kernel
  rw [lisEq_iff, toMat_lpow, toMat_lword] at h
  rw [h]
  ext i j
  rw [toMat_ltab]
  simp [neg_apply, one_apply, Fin.ext_iff, apply_ite]

/-! ### `2ρ` from the Mathlib Cartan matrices (review §8) -/

theorem E6_two_rho : rdE6.cartan *ᵥ ![16, 22, 30, 42, 30, 16] = fun _ => 2 := by
  decide +kernel

theorem E7_two_rho : rdE7.cartan *ᵥ ![34, 49, 66, 96, 75, 52, 27] = fun _ => 2 := by
  decide +kernel

theorem E8_two_rho : rdE8.cartan *ᵥ ![92, 136, 182, 270, 220, 168, 114, 58] = fun _ => 2 := by
  decide +kernel

/-! ### Golden-data lower bounds (kernel-established) -/

/-- Golden maximal orders. -/
def maximaE6 : List ℕ := [8, 9, 10, 12]
def maximaE7 : List ℕ := [8, 12, 14, 18, 30]
def maximaE8 : List ℕ := [14, 18, 20, 24, 30]

/-- Order certificates for the golden maximal orders. -/
def witnessesE6 : List (RawOrderCert 6) :=
  [⟨[0, 1, 2, 3, 4], ⟨[(2, 3)], 8⟩⟩,
   ⟨[0, 1, 3, 2, 4, 3, 5, 1, 4, 3, 2, 5], ⟨[(3, 2)], 9⟩⟩,
   ⟨[0, 1, 2, 3, 5], ⟨[(2, 1), (5, 1)], 10⟩⟩,
   ⟨[0, 1, 2, 3, 4, 5], ⟨[(2, 2), (3, 1)], 12⟩⟩]

def witnessesE7 : List (RawOrderCert 7) :=
  [⟨[0, 1, 2, 3, 4], ⟨[(2, 3)], 8⟩⟩,
   ⟨[0, 2, 3, 5, 6], ⟨[(2, 2), (3, 1)], 12⟩⟩,
   ⟨[0, 3, 6, 5, 1, 6, 2, 5, 3, 4, 2], ⟨[(2, 1), (7, 1)], 14⟩⟩,
   ⟨[0, 1, 2, 3, 4, 5, 6], ⟨[(2, 1), (3, 2)], 18⟩⟩,
   ⟨[5, 2, 4, 1, 0, 2, 5, 3, 6, 1, 4, 2, 3], ⟨[(2, 1), (3, 1), (5, 1)], 30⟩⟩]

def witnessesE8 : List (RawOrderCert 8) :=
  [⟨[0, 1, 3, 4, 5, 6, 7], ⟨[(2, 1), (7, 1)], 14⟩⟩,
   ⟨[0, 1, 2, 3, 4, 5, 6], ⟨[(2, 1), (3, 2)], 18⟩⟩,
   ⟨[0, 1, 2, 3, 5, 6, 7], ⟨[(2, 2), (5, 1)], 20⟩⟩,
   ⟨[0, 1, 2, 3, 4, 6, 7], ⟨[(2, 3), (3, 1)], 24⟩⟩,
   ⟨[0, 1, 2, 4, 5, 6, 7], ⟨[(2, 1), (3, 1), (5, 1)], 30⟩⟩]

theorem witnessesE6_ok : witnessesE6.all (checkOrderCert rdE6) = true := by decide +kernel
theorem witnessesE7_ok : witnessesE7.all (checkOrderCert rdE7) = true := by decide +kernel
theorem witnessesE8_ok : witnessesE8.all (checkOrderCert rdE8) = true := by decide +kernel

theorem mem_omega_of_witnesses {n : ℕ} {R : RootDatum n} {ws : List (RawOrderCert n)}
    (h : ws.all (checkOrderCert R) = true) {l : List ℕ} (hl : ws.map (·.order.val) = l) :
    ∀ m ∈ l, m ∈ omega R := by
  subst hl
  intro m hm
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hm
  exact mem_omega_of_checkOrderCert (List.all_eq_true.mp h c hc)

/-- **Golden lower bound, `W(E₆)`.** All of `1, 2, 3, 4, 5, 6, 8, 9, 10, 12` occur. -/
theorem E6_golden_subset_omega :
    (({1, 2, 3, 4, 5, 6, 8, 9, 10, 12} : Finset ℕ) : Set ℕ) ⊆ omega rdE6 := by
  have h := divisorsOf_subset_omega rdE6 (l := maximaE6) (by decide)
    (mem_omega_of_witnesses witnessesE6_ok rfl)
  rwa [show divisorsOf maximaE6 = {1, 2, 3, 4, 5, 6, 8, 9, 10, 12} by decide +kernel] at h

/-- **Golden lower bound, `W(E₇)`.** All of `1–10, 12, 14, 15, 18, 30` occur. -/
theorem E7_golden_subset_omega :
    (({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 18, 30} : Finset ℕ) : Set ℕ) ⊆ omega rdE7 := by
  have h := divisorsOf_subset_omega rdE7 (l := maximaE7) (by decide)
    (mem_omega_of_witnesses witnessesE7_ok rfl)
  rwa [show divisorsOf maximaE7 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 18, 30} by
    decide +kernel] at h

/-- **Golden lower bound, `W(E₈)`.** All of `1–10, 12, 14, 15, 18, 20, 24, 30` occur. -/
theorem E8_golden_subset_omega :
    (({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 18, 20, 24, 30} : Finset ℕ) : Set ℕ) ⊆
      omega rdE8 := by
  have h := divisorsOf_subset_omega rdE8 (l := maximaE8) (by decide)
    (mem_omega_of_witnesses witnessesE8_ok rfl)
  rwa [show divisorsOf maximaE8 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 18, 20, 24, 30} by
    decide +kernel] at h

/-! ### `E₆ ⊆ E₇ ⊆ E₈` for the witnessed order ideals (M3 acceptance, comparison engine) -/

/-- Layer: the witnessed `E₆` order ideal, stated exactly (as a set of orders, not as `ω(W(E₆))`). -/
def maskE6ideal : Mask := ⟨[1, 2, 3, 4, 5, 6, 8, 9, 10, 12], .exact, "witnessesE6 + K4"⟩
def maskE7ideal : Mask :=
  ⟨[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 18, 30], .exact, "witnessesE7 + K4"⟩

theorem maskE6ideal_eq : maskE6ideal.orders.toFinset = divisorsOf maximaE6 := by decide +kernel
theorem maskE7ideal_eq : maskE7ideal.orders.toFinset = divisorsOf maximaE7 := by decide +kernel
/-- Targets: witnessed maximal orders, a lower bound for the true spectrum. -/
def maskE7wit : Mask := ⟨maximaE7, .witnessedSubset, "witnessesE7"⟩
def maskE8wit : Mask := ⟨maximaE8, .witnessedSubset, "witnessesE8"⟩

theorem compare_E6_E7 :
    compare maskE6ideal maskE7wit = .contained
      [(1, 8), (2, 8), (3, 12), (4, 8), (5, 30), (6, 12), (8, 8), (9, 18), (10, 30), (12, 12)] := by
  decide +kernel

theorem compare_E7_E8 :
    compare maskE7ideal maskE8wit = .contained
      [(1, 14), (2, 14), (3, 18), (4, 20), (5, 20), (6, 18), (7, 14), (8, 24), (9, 18), (10, 20),
        (12, 24), (14, 14), (15, 30), (18, 18), (30, 30)] := by
  decide +kernel

theorem maskE7wit_holds : maskE7wit.Holds (omega rdE7) :=
  fun m hm => mem_omega_of_witnesses witnessesE7_ok rfl m hm

theorem maskE8wit_holds : maskE8wit.Holds (omega rdE8) :=
  fun m hm => mem_omega_of_witnesses witnessesE8_ok rfl m hm

/-- **Order-ideal containment** (never "embeds", K7): the witnessed `E₆` order ideal is contained
in `ω(W(E₇))`. -/
theorem E6_ideal_subset_omega_E7 : (divisorsOf maximaE6 : Set ℕ) ⊆ omega rdE7 := by
  refine compare_contained_sound compare_E6_E7 (ωL := (divisorsOf maximaE6 : Set ℕ)) ?_
    maskE7wit_holds (omega_posDownset rdE7)
  show {m | m ∈ maskE6ideal.orders} = _
  rw [← maskE6ideal_eq]
  ext m; simp

/-- **Order-ideal containment**: the witnessed `E₇` order ideal is contained in `ω(W(E₈))`. -/
theorem E7_ideal_subset_omega_E8 : (divisorsOf maximaE7 : Set ℕ) ⊆ omega rdE8 := by
  refine compare_contained_sound compare_E7_E8 (ωL := (divisorsOf maximaE7 : Set ℕ)) ?_
    maskE8wit_holds (omega_posDownset rdE8)
  show {m | m ∈ maskE7ideal.orders} = _
  rw [← maskE7ideal_eq]
  ext m; simp

end SpectrumVM

end
