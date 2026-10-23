import RequestProject.Dasein15VM.Walk
import RequestProject.Dasein15VM.UI.Proof
import RequestProject.Dasein15VM.UI.Wire

/-!
# RFC-0002 §9.3: the Dasein15 reference objects and edges

* `daseinEntry`: the certified 500-state trace `dasein500` (from `checkVMTrace_dasein`).
* `daseinObject`: the VM object `mkVMObject daseinSpec .dominantMass [daseinEntry]`.  Its mask is
  the observed mask (kind `witnessedSubset`), with orders `31, …, 62`
  (`daseinObject_mask_orders`), and its `maskHolds` is proved, not assumed.
* `dasein_spectrum`: the exact semantic order set of the Dasein15 spec for the dominant-class
  mass: `specOrders daseinSpec .dominantMass = {m | 21 ≤ m ≤ 63}` (Dasein15's `eigenspace` has
  no Clock prime, so the dominant mass of a mass-63 shape is at least `⌈63/3⌉ = 21`).
* `daseinExactObject`: the same spec and trace with the **declared** exact mask `21, …, 63`; its
  `Mask.Holds` hypothesis is discharged by `dasein_spectrum`.
* Synthetic targets `targetCover` (witnessed orders `42, …, 126`, order set their divisor
  closure) and `targetDiv60` (exact mask: the divisors of 60).
* Edges, kernel-checked:
  - `edgeContained : daseinExactObject → targetCover` is `contained`, hence
    `dasein_contained : {21..63} ⊆ divClosure {42..126}` via `compare_contained_sound`;
  - `edgeNotContained : daseinObject → targetDiv60` is `notContained 31`, hence
    `dasein_notContained : 31 ∈ specOrders daseinSpec .dominantMass ∧ 31 ∉ divisors of 60`;
  - `edgeUnknown : daseinObject → targetCover` is `unknown []`: a witnessed source against a
    witnessed target is never decided, even though every observed order is covered.
* `dasein_roundtrip`: the Dasein15 VM object serializes and deserializes to itself.
-/

namespace Dasein15VM.UI

open Dasein15 SpectrumVM

/-! ### The certified trace and the observed object -/

def daseinClaim : VerificationClaim :=
  ⟨"lean:Dasein15VM.dasein_VMCorrect", "lean:Dasein15VM.checkVMTrace_dasein", "lean4-v4.28.0"⟩

/-- The certified 500-state Dasein15 trace. -/
def daseinEntry : TraceEntry daseinSpec :=
  TraceEntry.ofCheck "dasein500" s₀ sFinal daseinTrace checkVMTrace_dasein daseinClaim

theorem daseinEntry_assurance : daseinEntry.assurance = .kernelEstablished := rfl

/-- The Dasein15 VM object (observed mask of the dominant-class mass). -/
def daseinObject : VMObject 15 :=
  mkVMObject daseinSpec .dominantMass [daseinEntry] daseinClaim

theorem daseinObject_mask_kind : daseinObject.mask.kind = .witnessedSubset := rfl

theorem daseinObject_specScoped : daseinObject.SpecScoped := rfl

set_option maxRecDepth 100000 in
/-- The observed orders of the walk: the dominant-class mass takes the values `31, …, 62`. -/
theorem daseinObject_mask_orders : daseinObject.mask.orders = List.range' 31 32 := by
  decide +kernel

/-- Every observed order is in the semantic order set (observed-mask soundness). -/
theorem daseinObject_observed_sound {m : ℕ} (hm : m ∈ daseinObject.mask.orders) :
    m ∈ specOrders daseinSpec .dominantMass :=
  daseinObject.maskHolds hm

/-! ### The exact order set of the Dasein15 spec -/

theorem classMass_sum {n : ℕ} (a : Fin n → ShapeClass) (v : PrimeShape n) :
    classMass a .Earth v + classMass a .Spoke v + classMass a .Hub v + classMass a .Clock v =
      mass v := by
  simp only [classMass_eq_sum, mass_eq_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  cases a i <;> simp

theorem classMass_clock_dasein (v : PrimeShape 15) : classMass eigenspace .Clock v = 0 := by
  rw [classMass_eq_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [if_neg]
  revert i; decide

/-- Witness shape of dominant mass `m` (for `21 ≤ m ≤ 63`): `m` on the prime 2 (Earth), the rest
split between 17 (Spoke) and 19 (Hub). -/
def spectrumWitness (m : ℕ) : PrimeShape 15 := fun i =>
  if i = 0 then m else if i = 6 then min m (63 - m) else if i = 7 then 63 - m - min m (63 - m)
  else 0

theorem spectrumWitness_spec :
    ∀ m ∈ List.range' 21 43, mass (spectrumWitness m) = 63 ∧
      classMass eigenspace (shapeClass eigenspace (spectrumWitness m)) (spectrumWitness m) = m := by
  decide +kernel

theorem classMass_shapeClass_le_mass {n : ℕ} (a : Fin n → ShapeClass) (v : PrimeShape n) :
    classMass a (shapeClass a v) v ≤ mass v := by
  have := classMass_sum a v
  cases shapeClass a v <;> omega

theorem dasein_dominant_ge (v : PrimeShape 15) (hv : mass v = 63) :
    21 ≤ classMass eigenspace (shapeClass eigenspace v) v := by
  have hsum := classMass_sum eigenspace v
  have hc := classMass_clock_dasein v
  have h1 := classMass_le_shapeClass eigenspace v .Earth
  have h2 := classMass_le_shapeClass eigenspace v .Spoke
  have h3 := classMass_le_shapeClass eigenspace v .Hub
  omega

theorem ofShape_invariant {n : ℕ} (S : VMSpec n) (v : PrimeShape n) (k : ℕ)
    (h : mass v = S.mass) : VMInvariant S (S.ofShape v k) := ⟨rfl, rfl, h⟩

theorem eval_dominant_ofShape {n : ℕ} (S : VMSpec n) (v : PrimeShape n) (k : ℕ) :
    Observable.eval S .dominantMass (S.ofShape v k) = classMass S.assign (shapeClass S.assign v) v :=
  rfl

theorem daseinSpec_assign : daseinSpec.assign = eigenspace := rfl

theorem daseinSpec_mass : daseinSpec.mass = 63 := rfl

/-- **The exact order set**: the dominant-class masses of invariant Dasein15 states are exactly
`21, …, 63`. -/
theorem dasein_spectrum : specOrders daseinSpec .dominantMass = {m | 21 ≤ m ∧ m ≤ 63} := by
  ext m
  constructor
  · rintro ⟨x, ⟨-, hcls, hmass⟩, rfl⟩
    have hd : Observable.eval daseinSpec .dominantMass x =
        classMass eigenspace (shapeClass eigenspace x.shape) x.shape := by
      simp only [Observable.eval]; rw [hcls]; rfl
    have hm : mass x.shape = 63 := hmass
    rw [Set.mem_setOf_eq, hd]
    exact ⟨dasein_dominant_ge _ hm, hm ▸ classMass_shapeClass_le_mass _ _⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨hm, hd⟩ := spectrumWitness_spec m (List.mem_range'_1.2 ⟨h1, by omega⟩)
    refine ⟨daseinSpec.ofShape (spectrumWitness m) 0,
      ofShape_invariant _ _ _ (hm.trans daseinSpec_mass.symm), ?_⟩
    rw [eval_dominant_ofShape, daseinSpec_assign]
    exact hd

/-- The declared exact mask `21, …, 63`. -/
def daseinExactMask : Mask := ⟨List.range' 21 43, .exact, "lean:Dasein15VM.UI.dasein_spectrum"⟩

theorem daseinExactMask_holds : daseinExactMask.Holds (specOrders daseinSpec .dominantMass) := by
  show {m | m ∈ List.range' 21 43} = _
  rw [dasein_spectrum]
  ext m
  simp only [List.mem_range'_1, Set.mem_setOf_eq]
  omega

def daseinExactClaim : VerificationClaim :=
  ⟨"lean:Dasein15VM.UI.daseinExactObject", "lean:Dasein15VM.UI.dasein_spectrum", "lean4-v4.28.0"⟩

/-- The Dasein15 object with the declared exact mask (hypothesis discharged by
`dasein_spectrum`). -/
def daseinExactObject : VMObject 15 :=
  declareVMObject daseinSpec .dominantMass [daseinEntry] daseinExactMask
    (specOrders daseinSpec .dominantMass) daseinExactMask_holds daseinExactClaim

/-! ### Synthetic targets -/

/-- Synthetic target orders `42, …, 126`. -/
def coverOrders : List ℕ := List.range' 42 85

def targetClaim (s : String) : VerificationClaim := ⟨s, "synthetic", "lean4-v4.28.0"⟩

/-- Synthetic target: witnessed orders `42, …, 126`; order set their divisor closure. -/
def targetCover : VMObject 15 :=
  declareVMObject daseinSpec .dominantMass [] ⟨coverOrders, .witnessedSubset, "synthetic:cover"⟩
    (divClosure {m | m ∈ coverOrders}) (subset_divClosure _) (targetClaim "synthetic:cover")

theorem targetCover_posDownset : PosDownset targetCover.omega :=
  fun m hm _ d hd => divClosure_isDivDownset _ m hm d hd

/-- The divisors of 60. -/
def div60 : List ℕ := [1, 2, 3, 4, 5, 6, 10, 12, 15, 20, 30, 60]

/-- Synthetic target: exact mask, the divisors of 60. -/
def targetDiv60 : VMObject 15 :=
  declareVMObject daseinSpec .dominantMass [] ⟨div60, .exact, "synthetic:div60"⟩
    {m | m ∈ div60} rfl (targetClaim "synthetic:div60")

/-! ### Guidance edges -/

def edgeContained : GuidanceEdge daseinExactObject targetCover := runCompare _ _

def edgeNotContained : GuidanceEdge daseinObject targetDiv60 := runCompare _ _

def edgeUnknown : GuidanceEdge daseinObject targetCover := runCompare _ _

theorem edgeContained_comparison :
    edgeContained.comparison = .contained ((List.range' 21 43).map fun a =>
      (a, if a < 42 then 2 * a else a)) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem edgeNotContained_comparison : edgeNotContained.comparison = .notContained 31 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem edgeUnknown_comparison : edgeUnknown.comparison = .unknown [] := by
  decide +kernel

/-- **Containment, kernel-checked**: every dominant-class mass of the Dasein15 spec divides one of
`42, …, 126`. -/
theorem dasein_contained :
    specOrders daseinSpec .dominantMass ⊆ divClosure {m | m ∈ coverOrders} :=
  edgeContained.contained_sound edgeContained_comparison targetCover_posDownset

/-- **Obstruction, kernel-checked**: the observed order `31` is a dominant-class mass of the
Dasein15 spec and is not a divisor of 60. -/
theorem dasein_notContained :
    31 ∈ specOrders daseinSpec .dominantMass ∧ 31 ∉ {m | m ∈ div60} :=
  edgeNotContained.notContained_sound edgeNotContained_comparison

theorem dasein_not_subset_div60 : ¬ specOrders daseinSpec .dominantMass ⊆ {m | m ∈ div60} :=
  edgeNotContained.notContained_not_subset edgeNotContained_comparison

/-- The `unknown` edge has no unresolved orders, and is still not a decision. -/
theorem edgeUnknown_status : edgeUnknown.comparison.status = .unknown := by
  rw [edgeUnknown_comparison]; rfl

/-! ### Proof terms -/

/-- The Dasein15 walk composed with the containment comparison, as a surface proof term. -/
def daseinProof : ProofTerm 15 :=
  .compose (.trace daseinSpec s₀ sFinal daseinTrace) (.compare daseinExactMask targetCover.mask)

theorem daseinProof_check : daseinProof.check = true := by
  simp only [daseinProof, ProofTerm.check, checkVMTrace_dasein, Bool.true_and]
  decide +kernel

theorem daseinProof_sound : daseinProof.denote := daseinProof.check_sound daseinProof_check

/-! ### Wire roundtrip -/

/-- **The Dasein15 VM object serializes and deserializes to itself** (the observed mask's
hypothesis is re-derived from the re-checked trace). -/
theorem dasein_roundtrip :
    (decodeObject 15 (encodeObject daseinObject "derived:observedMask_holds")).bind
      PreObject.attachObserved? = some daseinObject :=
  roundtrip_mkVMObject _ _ _ _ _

/-- The exact-mask object roundtrips with its hypothesis re-attached. -/
theorem daseinExact_roundtrip (ref : String) :
    decodeObject 15 (encodeObject daseinExactObject ref) = some (daseinExactObject.toPre ref) ∧
      (daseinExactObject.toPre ref).attach (specOrders daseinSpec .dominantMass)
        daseinExactMask_holds = daseinExactObject :=
  ⟨decodeObject_encodeObject _ _, rfl⟩

theorem edgeContained_roundtrip :
    decodeEdge daseinExactObject targetCover (encodeEdge edgeContained "a" "b") =
      some edgeContained :=
  decodeEdge_encodeEdge _ _ _

theorem edgeNotContained_roundtrip :
    decodeEdge daseinObject targetDiv60 (encodeEdge edgeNotContained "a" "b") =
      some edgeNotContained :=
  decodeEdge_encodeEdge _ _ _

end Dasein15VM.UI
