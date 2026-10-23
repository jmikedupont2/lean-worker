import RequestProject.Dasein15VM.UI.VMObject

/-!
# RFC-0002 §3.3 / §4.3: guidance edges

A guidance edge from a VM object `A` to a VM object `B` is the value `compare A.mask B.mask`.
Its meaning is fixed by `Verdict`:

* `contained ps`  — `A.omega ⊆ B.omega` (`compare_contained_sound`; needs `PosDownset B.omega`);
* `notContained a` — `¬ A.omega ⊆ B.omega`, and in fact `a ∈ A.omega ∧ a ∉ B.omega`
  (`compare_notContained_witness`);
* `unknown us`    — no claim (`Verdict` is `True`); every unresolved order is a source order
  without a covering target order (`compare_unknown_unresolved`).

The `Mask.Holds` hypotheses used are explicit parameters at the mask level (`compare_verdict`),
and at the object level they are the user-supplied fields `A.maskHolds`, `B.maskHolds`.
`derived_contained` composes two certified containments (open question 2).
-/

namespace Dasein15VM.UI

open SpectrumVM

/-- What a comparison verdict asserts about the two order sets. -/
def Verdict : Comparison → Set ℕ → Set ℕ → Prop
  | .contained _, ωL, ωT => ωL ⊆ ωT
  | .notContained _, ωL, ωT => ¬ ωL ⊆ ωT
  | .unknown _, _, _ => True

/-- Display status of an edge (S4–S6: three states, `unknown` is not a decision). -/
inductive EdgeStatus
  | contained
  | notContained
  | unknown
  deriving DecidableEq, Repr

def _root_.SpectrumVM.Comparison.status : Comparison → EdgeStatus
  | .contained _ => .contained
  | .notContained _ => .notContained
  | .unknown _ => .unknown

/-- Name of the soundness theorem behind a verdict (rendered next to the edge). -/
def _root_.SpectrumVM.Comparison.soundnessName : Comparison → String
  | .contained _ => "compare_contained_sound"
  | .notContained _ => "compare_notContained_sound"
  | .unknown _ => "unresolved"

/-- **Mask-level soundness** of `compare`, with every `Mask.Holds` an explicit parameter. -/
theorem compare_verdict {L T : Mask} {ωL ωT : Set ℕ} (hL : L.Holds ωL) (hT : T.Holds ωT)
    (hdown : PosDownset ωT) : Verdict (compare L T) ωL ωT := by
  cases h : compare L T with
  | contained ps => exact compare_contained_sound h hL hT hdown
  | notContained a => exact compare_notContained_sound h hL hT
  | unknown us => trivial

/-- **S5, strengthened**: the witness of `notContained` is a source order outside the target. -/
theorem compare_notContained_witness {L T : Mask} {ωL ωT : Set ℕ} {a : ℕ}
    (h : compare L T = .notContained a) (hL : L.Holds ωL) (hT : T.Holds ωT) :
    a ∈ ωL ∧ a ∉ ωT := by
  unfold SpectrumVM.compare at h
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
    refine ⟨L.mem_of_holds hL hLk hmem, fun haT => hfind ?_⟩
    unfold Mask.Holds at hT
    cases hT' : T.kind <;> rw [hT'] at hT
    · rw [← hT] at haT; exact haT
    · rw [hT'] at hk; exact absurd hk.2 (by decide)
    · exact hT haT
  · split_ifs at h

/-- **S6**: the orders listed by `unknown` are source orders with no covering target order. -/
theorem compare_unknown_unresolved {L T : Mask} {us : List ℕ} (h : compare L T = .unknown us) :
    ∀ a ∈ us, a ∈ L.orders ∧ coveringPair T a = none := by
  unfold SpectrumVM.compare at h
  split at h
  · cases h
  · split_ifs at h
    cases h
    intro a ha
    simp only [List.mem_filter, Option.isNone_iff_eq_none] at ha
    exact ha

/-! ### Guidance edges between VM objects -/

variable {n m k : ℕ}

/-- A guidance edge: the comparison of the two masks. -/
structure GuidanceEdge (A : VMObject n) (B : VMObject m) where
  comparison : Comparison
  computed : comparison = compare A.mask B.mask

/-- Draw an edge by running `compare`. -/
def runCompare (A : VMObject n) (B : VMObject m) : GuidanceEdge A B := ⟨_, rfl⟩

namespace GuidanceEdge

variable {A : VMObject n} {B : VMObject m}

/-- Edges are determined by their endpoints. -/
theorem ext_eq (e : GuidanceEdge A B) : e = runCompare A B := by
  cases e with | mk c h => subst h; rfl

/-- **Edge soundness**: under the objects' `Mask.Holds` hypotheses (and divisor-closure of the
target order set), the edge's verdict holds. -/
theorem sound (e : GuidanceEdge A B) (hdown : PosDownset B.omega) :
    Verdict e.comparison A.omega B.omega :=
  e.computed ▸ compare_verdict A.maskHolds B.maskHolds hdown

/-- **S4**: a `contained` edge proves containment. -/
theorem contained_sound (e : GuidanceEdge A B) {ps : List (ℕ × ℕ)}
    (h : e.comparison = .contained ps) (hdown : PosDownset B.omega) : A.omega ⊆ B.omega :=
  compare_contained_sound (e.computed ▸ h) A.maskHolds B.maskHolds hdown

/-- The covering pairs of a `contained` edge are genuine. -/
theorem contained_pairs (e : GuidanceEdge A B) {ps : List (ℕ × ℕ)}
    (h : e.comparison = .contained ps) :
    ∀ p ∈ ps, p.1 ∈ A.mask.orders ∧ p.2 ∈ B.mask.orders ∧ p.1 ∣ p.2 :=
  compare_contained_pairs (e.computed ▸ h)

/-- **S5**: a `notContained` edge proves non-containment, with its witness. -/
theorem notContained_sound (e : GuidanceEdge A B) {a : ℕ}
    (h : e.comparison = .notContained a) : a ∈ A.omega ∧ a ∉ B.omega :=
  compare_notContained_witness (e.computed ▸ h) A.maskHolds B.maskHolds

theorem notContained_not_subset (e : GuidanceEdge A B) {a : ℕ}
    (h : e.comparison = .notContained a) : ¬ A.omega ⊆ B.omega :=
  compare_notContained_sound (e.computed ▸ h) A.maskHolds B.maskHolds

/-- **S6**: an `unknown` edge lists its unresolved orders. -/
theorem unknown_unresolved (e : GuidanceEdge A B) {us : List ℕ}
    (h : e.comparison = .unknown us) : ∀ a ∈ us, a ∈ A.mask.orders ∧ coveringPair B.mask a = none :=
  compare_unknown_unresolved (e.computed ▸ h)

/-- A `contained` edge carries a badge for `A.omega ⊆ B.omega`. -/
def containedBadge (e : GuidanceEdge A B) {ps : List (ℕ × ℕ)} (h : e.comparison = .contained ps)
    (hdown : PosDownset B.omega) (claim : VerificationClaim) : Badge (A.omega ⊆ B.omega) :=
  Badge.ofProof claim (e.contained_sound h hdown)

/-- A `notContained` edge carries a badge for `¬ A.omega ⊆ B.omega`. -/
def notContainedBadge (e : GuidanceEdge A B) {a : ℕ} (h : e.comparison = .notContained a)
    (claim : VerificationClaim) : Badge (¬ A.omega ⊆ B.omega) :=
  Badge.ofProof claim (e.notContained_not_subset h)

end GuidanceEdge

/-- **Derived edge** (open question 2): two certified containments through the same middle
object compose.  Both edges use the middle object's own `maskHolds`, so the hypotheses are
compatible by construction.  The result is a *derived* containment, not a `compare` verdict. -/
theorem derived_contained {A : VMObject n} {B : VMObject m} {C : VMObject k}
    (e₁ : GuidanceEdge A B) (e₂ : GuidanceEdge B C) {ps qs : List (ℕ × ℕ)}
    (h₁ : e₁.comparison = .contained ps) (h₂ : e₂.comparison = .contained qs)
    (hB : PosDownset B.omega) (hC : PosDownset C.omega) : A.omega ⊆ C.omega :=
  (e₁.contained_sound h₁ hB).trans (e₂.contained_sound h₂ hC)

end Dasein15VM.UI
