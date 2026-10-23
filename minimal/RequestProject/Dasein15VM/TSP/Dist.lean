import RequestProject.Dasein15VM.TSP.City

/-!
# RFC-0004 §3.2: spectral distance (a directed cost, not a metric)

A **pivot** for the directed edge `a → b` is a shared divisor of `a` and `b`, i.e. an element of
`divClosure {a} ∩ divClosure {b}` (SpectrumVM's divisibility closure).  Its **depth** is the
number of prime factors (with multiplicity) removed when refining `a` down to the pivot,
`Ω (a / d)`.  The edge first refines `a` down to a pivot and then makes one divisibility step up
to `b`; its cost is the minimal pivot depth plus one:

* `PivotAt a b k`: some pivot has depth `≤ k`;
* `pivot_exists a b`: a pivot exists (the gcd), so `Nat.find` is well-founded (S10);
* `pivotDepth a b := Nat.find (pivot_exists a b)` and `massDist a b := pivotDepth a b + 1`;
* `spectralDist c₁ c₂ := massDist c₁.mass c₂.mass` on cities;
* `massDist_eq_distC`: the closed form `Ω (a / gcd a b) + 1` (`distC`, kernel-computable);
* `massDist_of_dvd`: a direct divisibility `a ∣ b` costs `1`;
* `spectralDist_asymm`: the witness `21 → 42` costs `1` while `42 → 21` costs `2` (S11).

**Deviation from the RFC.** The RFC's `pivot_exists` asks for a shared pivot *in the carrier that
both cities divide* (a common multiple).  That is false for the Dasein15 carrier:
`rfc_pivot_exists_false` shows that `22` and `23` have no common multiple in `{21, …, 63}`.
Pivots are therefore taken in the divisibility closure (common divisors), where they always
exist.  The RFC's first two clauses (`c₁ ∣ c₂ → 1`, `c₂ ∣ c₁ → 1`) would also make the cost
symmetric on comparable pairs; here only `c₁ ∣ c₂` gives cost `1`.
-/

namespace Dasein15VM.TSP

open SpectrumVM

variable {n : ℕ}

/-- Some pivot (a shared divisor) of the edge `a → b` has depth at most `k`. -/
def PivotAt (a b k : ℕ) : Prop :=
  ∃ d ∈ divClosure {a} ∩ divClosure {b}, (a / d).primeFactorsList.length ≤ k

theorem mem_divClosure_singleton {a d : ℕ} : d ∈ divClosure {a} ↔ d ∣ a := by
  simp [divClosure]

/-- **`pivot_exists`** (S10): every edge has a pivot — the gcd. -/
theorem pivot_exists (a b : ℕ) : ∃ k, PivotAt a b k :=
  ⟨_, Nat.gcd a b, ⟨mem_divClosure_singleton.2 (Nat.gcd_dvd_left a b),
    mem_divClosure_singleton.2 (Nat.gcd_dvd_right a b)⟩, le_rfl⟩

open Classical in
/-- Minimal pivot depth of the edge `a → b`. -/
noncomputable def pivotDepth (a b : ℕ) : ℕ := Nat.find (pivot_exists a b)

/-- Directed spectral cost of `a → b`: minimal pivot depth, plus the final divisibility step. -/
noncomputable def massDist (a b : ℕ) : ℕ := pivotDepth a b + 1

/-- Kernel-computable closed form of `massDist`. -/
def distC (a b : ℕ) : ℕ := (a / Nat.gcd a b).primeFactorsList.length + 1

theorem div_dvd_div_of_dvd {a d g : ℕ} (hdg : d ∣ g) (hga : g ∣ a) : a / g ∣ a / d := by
  obtain ⟨r, rfl⟩ := hdg
  obtain ⟨q, rfl⟩ := hga
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  rw [Nat.mul_assoc, Nat.mul_div_cancel_left _ hd, ← Nat.mul_assoc,
    Nat.mul_div_cancel_left _ (by positivity)]
  exact Dvd.intro_left r rfl

/-- The pivot depth is attained at the gcd. -/
theorem pivotDepth_eq (a b : ℕ) : pivotDepth a b = (a / Nat.gcd a b).primeFactorsList.length := by
  classical
  apply le_antisymm
  · exact Nat.find_min' _ ⟨Nat.gcd a b, ⟨mem_divClosure_singleton.2 (Nat.gcd_dvd_left a b),
      mem_divClosure_singleton.2 (Nat.gcd_dvd_right a b)⟩, le_rfl⟩
  · obtain ⟨d, ⟨hda, hdb⟩, hk⟩ := Nat.find_spec (pivot_exists a b)
    rw [mem_divClosure_singleton] at hda hdb
    refine le_trans ?_ hk
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp
    have hd0 : d ≠ 0 := by rintro rfl; simp at hda; omega
    apply List.Sublist.length_le
    apply Nat.primeFactorsList_sublist_of_dvd
      (div_dvd_div_of_dvd (Nat.dvd_gcd hda hdb) (Nat.gcd_dvd_left a b))
    exact (Nat.div_pos (Nat.le_of_dvd ha hda) (Nat.pos_of_ne_zero hd0)).ne'

theorem massDist_eq_distC (a b : ℕ) : massDist a b = distC a b := by
  rw [massDist, distC, pivotDepth_eq]

/-- A direct divisibility step costs `1`. -/
theorem massDist_of_dvd {a b : ℕ} (h : a ∣ b) : massDist a b = 1 := by
  rw [massDist_eq_distC, distC, Nat.gcd_eq_left h]
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  · simp [Nat.div_self ha]

/-- Every edge costs at least `1`. -/
theorem one_le_massDist (a b : ℕ) : 1 ≤ massDist a b := Nat.le_add_left 1 _

/-- Directed spectral distance between cities. -/
noncomputable def spectralDist {S : VMSpec n} (c₁ c₂ : City S) : ℕ := massDist c₁.mass c₂.mass

theorem spectralDist_eq {S : VMSpec n} (c₁ c₂ : City S) :
    spectralDist c₁ c₂ = distC c₁.mass c₂.mass := massDist_eq_distC _ _

theorem mem_range'_21 {m : ℕ} (h1 : 21 ≤ m) (h2 : m ≤ 63) : m ∈ List.range' 21 43 :=
  List.mem_range'_1.2 ⟨h1, by omega⟩

/-- **Asymmetry witness** (acceptance criterion 3, S11): `21 → 42` costs `1`, `42 → 21` costs `2`. -/
theorem spectralDist_asymm :
    spectralDist (daseinCity 21 (mem_range'_21 le_rfl (by norm_num)))
        (daseinCity 42 (mem_range'_21 (by norm_num) (by norm_num))) = 1 ∧
      spectralDist (daseinCity 42 (mem_range'_21 (by norm_num) (by norm_num)))
        (daseinCity 21 (mem_range'_21 le_rfl (by norm_num))) = 2 := by
  constructor <;> rw [spectralDist_eq] <;> decide +kernel

theorem spectralDist_not_symm :
    ∃ c₁ c₂ : City daseinSpec, spectralDist c₁ c₂ ≠ spectralDist c₂ c₁ :=
  ⟨_, _, by rw [spectralDist_asymm.1, spectralDist_asymm.2]; decide⟩

/-- The RFC's literal `pivot_exists` (a common multiple *in the carrier*) fails for the Dasein15
carrier: `22` and `23` are cities with no common multiple in `{21, …, 63}`. -/
theorem rfc_pivot_exists_false :
    22 ∈ carrier daseinSpec ∧ 23 ∈ carrier daseinSpec ∧
      ¬ ∃ m ∈ carrier daseinSpec, 22 ∣ m ∧ 23 ∣ m := by
  refine ⟨mem_carrier_dasein.2 (by omega), mem_carrier_dasein.2 (by omega), ?_⟩
  rintro ⟨m, hm, h22, h23⟩
  rw [mem_carrier_dasein] at hm
  have : 22 * 23 ∣ m := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h22 h23
  have := Nat.le_of_dvd (by omega) this
  omega

end Dasein15VM.TSP
