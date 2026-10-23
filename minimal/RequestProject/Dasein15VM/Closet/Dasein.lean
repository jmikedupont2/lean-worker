import RequestProject.Dasein15VM.Closet.Basic

/-!
# The Dasein15 closet, and what the build says about the Monster's closet

* `walkMoonshine`: the Dasein15 walk's moonshine — spectrum `{31, …, 62}` (the dominant masses
  observed along the certified walk, `daseinObject_mask_orders`).
* `exactMoonshine`: the exact moonshine — spectrum the whole carrier `{21, …, 63}`.
* `daseinCloset`: the closet of `daseinSpec` holding both (laminar: `walk ⊆ exact`), with
  `daseinCloset_colimit` (`= {21, …, 63}`) and `daseinCloset_limit` (`= {31, …, 62}`, the core is
  the walk's moonshine).
* `emptyCloset`, `emptyCloset_ne`: two different closets of the same object (the closet is not a
  field of the object).
* `not_related_of_87` / `not_mem_closet_of_87`: a moonshine whose spectrum contains the Monster's
  home pivot `87` is not spectrally related to `daseinSpec`, so it is in no closet of it.
* Tower spectra, as finite prefixes listed in the request (`golaySpectrum = {0, 8, 12, 16, 24}`,
  `leechPrefix = {0, 4, 6, …, 24}`, `voaPrefix = {1, 196884, 21493760}`):
  - `tower_not_related_dasein`: none of them lies in the Dasein15 carrier, so none can be in a
    Dasein15 closet;
  - `golay_subset_leech`, `leech_not_subset_voa`, `golay_disjoint_voa`, `leech_disjoint_voa`:
    the three are pairwise laminar, but the chain `Golay ⊆ Leech ⊆ VOA` fails and the
    intersection of the three is empty (`tower_inter_empty`), so their limit is not the Golay
    spectrum.
-/

namespace Dasein15VM.Closet

open Dasein15 SpectrumVM TSP UI

/-- The Dasein15 walk's moonshine. -/
def walkMoonshine : Moonshine 15 where
  spec := daseinSpec
  spectrum := {m | 31 ≤ m ∧ m ≤ 62}
  exp := finalExp
  rel := fun m hm => mem_carrier_dasein.2 ⟨by have := hm.1; omega, by have := hm.2; omega⟩
  provenance := daseinClaim

/-- The walk moonshine's spectrum is the observed mask of the certified walk. -/
theorem walkMoonshine_spectrum :
    walkMoonshine.spectrum = {m | m ∈ daseinObject.mask.orders} := by
  rw [daseinObject_mask_orders]
  ext m
  simp only [walkMoonshine, Set.mem_setOf_eq, List.mem_range'_1]
  omega

/-- The exact moonshine: the whole Dasein15 carrier. -/
def exactMoonshine : Moonshine 15 where
  spec := daseinSpec
  spectrum := carrier daseinSpec
  exp := finalExp
  rel := subset_rfl
  provenance := daseinExactClaim

theorem walk_subset_exact : walkMoonshine.spectrum ⊆ exactMoonshine.spectrum :=
  walkMoonshine.rel

/-- The Dasein15 closet. -/
def daseinCloset : Closet daseinSpec where
  moonshines := [walkMoonshine, exactMoonshine]
  related := by
    intro M hM
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hM
    rcases hM with rfl | rfl
    · exact ⟨walkMoonshine.rel⟩
    · exact ⟨exactMoonshine.rel⟩
  coherent := by
    intro M₁ h₁ M₂ h₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h₁ h₂
    rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl
    · exact Or.inl subset_rfl
    · exact Or.inl walk_subset_exact
    · exact Or.inr (Or.inl walk_subset_exact)
    · exact Or.inl subset_rfl

theorem daseinCloset_colimit : daseinCloset.colimit = {m | 21 ≤ m ∧ m ≤ 63} := by
  apply Set.Subset.antisymm
  · rw [← carrier_dasein]; exact daseinCloset.colimit_subset_carrier
  · intro m hm
    exact ⟨exactMoonshine, by simp [daseinCloset], mem_carrier_dasein.2 hm⟩

theorem daseinCloset_limit : daseinCloset.limit = walkMoonshine.spectrum := by
  apply Set.Subset.antisymm
  · intro m hm; exact hm walkMoonshine (by simp [daseinCloset])
  · intro m hm M hM
    simp only [daseinCloset, List.mem_cons, List.not_mem_nil, or_false] at hM
    rcases hM with rfl | rfl
    · exact hm
    · exact walk_subset_exact hm

/-- The empty closet of the Dasein15 spec. -/
def emptyCloset : Closet daseinSpec := ⟨[], by simp, by simp⟩

/-- The same object has different closets. -/
theorem emptyCloset_ne : emptyCloset ≠ daseinCloset := by
  intro h
  have := congrArg Closet.moonshines h
  simp [emptyCloset, daseinCloset] at this

/-- A moonshine containing the Monster's home pivot is not related to the Dasein15 spec. -/
theorem not_related_of_87 {M : Moonshine 15} (h : 87 ∈ M.spectrum) :
    ¬ SpectralRel daseinSpec M := fun hr => monster_off_dasein_carrier (hr.related h)

theorem not_mem_closet_of_87 (C : Closet daseinSpec) {M : Moonshine 15} (h : 87 ∈ M.spectrum) :
    M ∉ C.moonshines := fun hM => not_related_of_87 h (C.related M hM)

/-! ### Tower spectra (finite prefixes as listed in the request) -/

def golaySpectrum : Set ℕ := ↑({0, 8, 12, 16, 24} : Finset ℕ)
def leechPrefix : Set ℕ := ↑({0, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24} : Finset ℕ)
def voaPrefix : Set ℕ := ↑({1, 196884, 21493760} : Finset ℕ)

/-- No tower spectrum lies in the Dasein15 carrier. -/
theorem tower_not_related_dasein :
    ¬ golaySpectrum ⊆ carrier daseinSpec ∧ ¬ leechPrefix ⊆ carrier daseinSpec ∧
      ¬ voaPrefix ⊆ carrier daseinSpec := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := mem_carrier_dasein.1 (h (show 0 ∈ golaySpectrum by simp [golaySpectrum])); omega
  · have := mem_carrier_dasein.1 (h (show 0 ∈ leechPrefix by simp [leechPrefix])); omega
  · have := mem_carrier_dasein.1 (h (show 1 ∈ voaPrefix by simp [voaPrefix])); omega

theorem golay_subset_leech : golaySpectrum ⊆ leechPrefix := by
  simp only [golaySpectrum, leechPrefix, Finset.coe_subset]; decide

theorem leech_not_subset_voa : ¬ leechPrefix ⊆ voaPrefix := by
  simp only [leechPrefix, voaPrefix, Finset.coe_subset]; decide

theorem golay_disjoint_voa : Disjoint golaySpectrum voaPrefix := by
  simp only [golaySpectrum, voaPrefix, Finset.disjoint_coe]; decide

theorem leech_disjoint_voa : Disjoint leechPrefix voaPrefix := by
  simp only [leechPrefix, voaPrefix, Finset.disjoint_coe]; decide

/-- The three tower spectra are pairwise laminar. -/
theorem tower_laminar :
    Laminar golaySpectrum leechPrefix ∧ Laminar golaySpectrum voaPrefix ∧
      Laminar leechPrefix voaPrefix :=
  ⟨Or.inl golay_subset_leech, Or.inr (Or.inr golay_disjoint_voa),
    Or.inr (Or.inr leech_disjoint_voa)⟩

/-- Their intersection is empty: the limit of the three is not the Golay spectrum. -/
theorem tower_inter_empty : golaySpectrum ∩ leechPrefix ∩ voaPrefix = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 fun m ⟨⟨h1, _⟩, h3⟩ => ?_
  exact Set.disjoint_left.1 golay_disjoint_voa h1 h3

end Dasein15VM.Closet
