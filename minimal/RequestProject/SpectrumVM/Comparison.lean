module

public import RequestProject.SpectrumVM.OrderIdeal
public import RequestProject.SpectrumVM.Spectrum

/-!
# SpectrumVM §9: masks and three-valued comparison (theorem M1)

A `Mask` is a finite list of orders plus a *declared* kind and a provenance string.  The declared
kind is not evidence: every theorem below takes the semantic statement `Mask.Holds M ω` (what the
kind claims about the true spectrum `ω`) as an explicit hypothesis, so a conclusion drawn from an
imported "exact" class list is conditional on that imported claim (review §6/§7).

One soundness lemma per row of the RFC §9 table (M1), plus soundness of the engine `compare`.
Spectra are compared through the positive downset property `PosDownset`, which every
`omega R` satisfies (K4).
-/

@[expose] public section

namespace SpectrumVM

inductive MaskKind
  | exact
  | witnessedSubset
  | outerBound
  deriving DecidableEq, Repr

structure Mask where
  orders : List ℕ
  kind : MaskKind
  provenance : String
  deriving Repr

/-- What the declared kind of a mask asserts about a true spectrum `ω`. -/
def Mask.Holds (M : Mask) (ω : Set ℕ) : Prop :=
  match M.kind with
  | .exact => {m | m ∈ M.orders} = ω
  | .witnessedSubset => {m | m ∈ M.orders} ⊆ ω
  | .outerBound => ω ⊆ {m | m ∈ M.orders}

/-- Downward closure under divisibility, for positive members (the form of K4). -/
def PosDownset (ω : Set ℕ) : Prop := ∀ m ∈ ω, 0 < m → ∀ d, d ∣ m → d ∈ ω

/-- Every spectrum `omega R` is a positive downset (K4). -/
theorem omega_posDownset {n : ℕ} (R : RootDatum n) : PosDownset (omega R) :=
  fun _ hm hpos _ hd => omega_dvd_closed R hm hpos hd

/-- Evidence that an order occurs in the layer (exact or witnessed). -/
theorem Mask.mem_of_holds {M : Mask} {ω : Set ℕ} (h : M.Holds ω) (hk : M.kind ≠ .outerBound)
    {a : ℕ} (ha : a ∈ M.orders) : a ∈ ω := by
  unfold Mask.Holds at h
  cases hM : M.kind <;> rw [hM] at h
  · exact h ▸ ha
  · exact h ha
  · exact absurd hM hk

/-! ### M1, one lemma per row -/

/-- Row 1 (exact / exact): containment is decided by the finite data. -/
theorem M1_exact_exact {L T : Mask} {ωL ωT : Set ℕ} (hLk : L.kind = .exact) (hTk : T.kind = .exact)
    (hL : L.Holds ωL) (hT : T.Holds ωT) : ωL ⊆ ωT ↔ ∀ a ∈ L.orders, a ∈ T.orders := by
  unfold Mask.Holds at hL hT
  rw [hLk] at hL; rw [hTk] at hT
  subst hL hT
  rfl

/-- Row 2 (observed subset / exact): a witnessed layer order absent from an exact target
disproves containment. -/
theorem M1_observed_exact {L T : Mask} {ωL ωT : Set ℕ} (hLk : L.kind ≠ .outerBound)
    (hTk : T.kind = .exact) (hL : L.Holds ωL) (hT : T.Holds ωT) {a : ℕ} (ha : a ∈ L.orders)
    (haT : a ∉ T.orders) : ¬ ωL ⊆ ωT := by
  intro hsub
  have := hsub (L.mem_of_holds hL hLk ha)
  unfold Mask.Holds at hT; rw [hTk] at hT
  rw [← hT] at this
  exact haT this

/-- Row 3 (exact / witnessed subset): if every layer order divides a positive witnessed target
order, containment holds (for a target spectrum closed under divisors). -/
theorem M1_exact_witnessed {L T : Mask} {ωL ωT : Set ℕ} (hLk : L.kind = .exact)
    (hTk : T.kind ≠ .outerBound) (hL : L.Holds ωL) (hT : T.Holds ωT) (hdown : PosDownset ωT)
    (hcov : ∀ a ∈ L.orders, ∃ b ∈ T.orders, 0 < b ∧ a ∣ b) : ωL ⊆ ωT := by
  unfold Mask.Holds at hL; rw [hLk] at hL
  subst hL
  intro a ha
  obtain ⟨b, hb, hbpos, hab⟩ := hcov a ha
  exact hdown b (T.mem_of_holds hT hTk hb) hbpos a hab

/-- Row 4 (either / outer bound): a witnessed layer order outside a certified upper bound of the
target proves an obstruction. -/
theorem M1_outerBound {L T : Mask} {ωL ωT : Set ℕ} (hLk : L.kind ≠ .outerBound)
    (hTk : T.kind = .outerBound) (hL : L.Holds ωL) (hT : T.Holds ωT) {a : ℕ} (ha : a ∈ L.orders)
    (haT : a ∉ T.orders) : ¬ ωL ⊆ ωT := by
  intro hsub
  have := hsub (L.mem_of_holds hL hLk ha)
  unfold Mask.Holds at hT; rw [hTk] at hT
  exact haT (hT this)

/-! ### The comparison engine (IDEAL.COMPARE) -/

inductive Comparison
  | contained (pairs : List (ℕ × ℕ))
  | notContained (witness : ℕ)
  | unknown (unresolved : List ℕ)
  deriving DecidableEq, Repr

/-- Can the target data refute a layer order (exact or outer bound target)? -/
def MaskKind.refutes : MaskKind → Bool
  | .exact => true
  | .outerBound => true
  | .witnessedSubset => false

/-- Is the target data a lower bound for the target spectrum? -/
def MaskKind.witnesses : MaskKind → Bool
  | .outerBound => false
  | _ => true

def coveringPair (T : Mask) (a : ℕ) : Option (ℕ × ℕ) :=
  (T.orders.find? fun b => decide (0 < b) && decide (a ∣ b)).map fun b => (a, b)

/-- Three-valued comparison of a layer against a target. -/
def compare (L T : Mask) : Comparison :=
  match (if L.kind.witnesses && T.kind.refutes then
      L.orders.find? fun a => !(T.orders.contains a) else none) with
  | some a => .notContained a
  | none =>
    if L.kind = .exact && T.kind.witnesses &&
        L.orders.all (fun a => (coveringPair T a).isSome) then
      .contained (L.orders.filterMap (coveringPair T))
    else
      .unknown (L.orders.filter fun a => (coveringPair T a).isNone)

theorem compare_notContained_sound {L T : Mask} {ωL ωT : Set ℕ} {a : ℕ}
    (h : compare L T = .notContained a) (hL : L.Holds ωL) (hT : T.Holds ωT) : ¬ ωL ⊆ ωT := by
  unfold compare at h
  split at h
  · rename_i b hb
    cases h
    split_ifs at hb with hk
    have hfind := List.find?_some hb
    have hmem := List.mem_of_find?_eq_some hb
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.contains_eq_mem,
      decide_eq_false_iff_not] at hfind
    simp only [Bool.and_eq_true] at hk
    have hLk : L.kind ≠ .outerBound := by
      intro h'; rw [h'] at hk; exact absurd hk.1 (by decide)
    cases hT' : T.kind
    · exact M1_observed_exact hLk hT' hL hT hmem hfind
    · rw [hT'] at hk; exact absurd hk.2 (by decide)
    · exact M1_outerBound hLk hT' hL hT hmem hfind
  · split_ifs at h

theorem compare_contained_sound {L T : Mask} {ωL ωT : Set ℕ} {ps : List (ℕ × ℕ)}
    (h : compare L T = .contained ps) (hL : L.Holds ωL) (hT : T.Holds ωT)
    (hdown : PosDownset ωT) : ωL ⊆ ωT := by
  unfold compare at h
  split at h
  · cases h
  · split_ifs at h with hk
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hk
    obtain ⟨⟨hLk, hTk⟩, hcov⟩ := hk
    have hTk' : T.kind ≠ .outerBound := by intro h'; rw [h'] at hTk; exact absurd hTk (by decide)
    refine M1_exact_witnessed hLk hTk' hL hT hdown fun a ha => ?_
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (hcov a ha)
    unfold coveringPair at hp
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hp
    have := List.find?_some hb
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact ⟨b, List.mem_of_find?_eq_some hb, this⟩

/-- Every pair reported by `contained` is a genuine covering pair `(a, b)` with `a ∣ b`. -/
theorem compare_contained_pairs {L T : Mask} {ps : List (ℕ × ℕ)}
    (h : compare L T = .contained ps) : ∀ p ∈ ps, p.1 ∈ L.orders ∧ p.2 ∈ T.orders ∧ p.1 ∣ p.2 := by
  unfold compare at h
  split at h
  · cases h
  · split_ifs at h
    cases h
    intro p hp
    obtain ⟨a, ha, hp⟩ := List.mem_filterMap.mp hp
    unfold coveringPair at hp
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hp
    have := List.find?_some hb
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact ⟨ha, List.mem_of_find?_eq_some hb, this.2⟩

/-! ### Obstruction reports (review §7) -/

/-- Layer orders absent from the supplied target data.  This is a certified obstruction list only
when the layer data is witnessed and the target data is exact or an outer bound
(`obstruction_sound`); otherwise it is merely "observed source orders absent from target data". -/
def absentOrders (L T : Mask) : List ℕ := L.orders.filter fun a => !(T.orders.contains a)

/-- Divisibility-minimal elements of a list (the simplest obstruction orders). -/
def dvdMinimal (l : List ℕ) : List ℕ := l.filter fun a => l.all fun b => !(b ∣ a) || b == a

theorem obstruction_sound {L T : Mask} {ωL ωT : Set ℕ} (hL : L.Holds ωL) (hT : T.Holds ωT)
    (hLk : L.kind ≠ .outerBound) (hTk : T.kind ≠ .witnessedSubset) :
    ∀ a ∈ absentOrders L T, a ∈ ωL ∧ a ∉ ωT := by
  intro a ha
  simp only [absentOrders, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true,
    List.contains_eq_mem, decide_eq_false_iff_not] at ha
  refine ⟨L.mem_of_holds hL hLk ha.1, fun haT => ha.2 ?_⟩
  unfold Mask.Holds at hT
  cases hT' : T.kind <;> rw [hT'] at hT
  · rw [← hT] at haT; exact haT
  · exact absurd hT' hTk
  · exact hT haT

end SpectrumVM

end
