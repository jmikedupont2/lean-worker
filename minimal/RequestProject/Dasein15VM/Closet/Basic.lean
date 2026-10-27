import RequestProject.Dasein15VM.TSP.City

/-!
# Objects, closets and the spectral moonshine panorama

The objects are VM specs `X : VMSpec n` (RFC-0003's `FamilyObject` is not built; a closet only
uses the object's carrier, `TSP.carrier X`).

* `Moonshine n`: a spec, a spectrum `Set ℕ`, an exponent vector, the realizability field
  `rel : spectrum ⊆ carrier spec`, and a provenance claim.
* `SpectralRel X M`: `M.spectrum ⊆ carrier X`.  `SpectralRel.mono` (contravariance in the
  spectrum: the panorama's functor action), `SpectralRel.of_carrier_subset`, and
  `spectralRel_withRoute` (the route does not matter).
* `Laminar A B`: `A ⊆ B ∨ B ⊆ A ∨ Disjoint A B`.  The RFC's literal condition
  `A ⊆ B ∨ B ⊆ A ∨ (A ⊄ B ∧ B ⊄ A)` is a tautology (`rfc_coherent_tautology`) and constrains
  nothing; the closet uses the laminar condition the text describes.
* `Closet X`: a list of moonshines, each spectrally related to `X`, pairwise laminar.  The
  closet is a separate structure, not a field of `X`.
* The panorama: `Closet.Obj C` (the moonshines of the closet) is preordered by spectral
  containment, hence a (thin) category through Mathlib's `Preorder.smallCategory`.
  - `Closet.colimit C` (union) and `Closet.limit C` (intersection), with `isLUB_colimit` and
    `isGLB_limit`;
  - `Closet.colimit_subset_carrier`: the global consequence of the local `related` proofs;
  - `Closet.limit_subset_carrier` for a nonempty closet, while `Closet.limit_nil` /
    `Closet.limit_nil_not_subset_carrier` show that the empty closet has limit `univ`, which is
    not inside the (finite) carrier;
  - `Closet.exists_core`: in a nonempty closet with nonempty limit, the limit is the spectrum of
    one of its moonshines (the core).
-/

namespace Dasein15VM.Closet

open SpectrumVM TSP

variable {n : ℕ}

/-- A moonshine object. -/
structure Moonshine (n : ℕ) where
  spec : VMSpec n
  spectrum : Set ℕ
  exp : PrimeShape n
  rel : spectrum ⊆ carrier spec
  provenance : VerificationClaim

/-- The spectral relation between an object and a moonshine. -/
structure SpectralRel (X : VMSpec n) (M : Moonshine n) : Prop where
  related : M.spectrum ⊆ carrier X

/-- Every moonshine is spectrally related to its own spec. -/
theorem SpectralRel.self (M : Moonshine n) : SpectralRel M.spec M := ⟨M.rel⟩

/-- Contravariance: a smaller spectrum inherits the relation. -/
theorem SpectralRel.mono {X : VMSpec n} {M₁ M₂ : Moonshine n} (h : M₁.spectrum ⊆ M₂.spectrum)
    (h₂ : SpectralRel X M₂) : SpectralRel X M₁ := ⟨h.trans h₂.related⟩

theorem SpectralRel.of_carrier_subset {X Y : VMSpec n} {M : Moonshine n}
    (hXY : carrier X ⊆ carrier Y) (h : SpectralRel X M) : SpectralRel Y M :=
  ⟨h.related.trans hXY⟩

theorem spectralRel_withRoute {X : VMSpec n} (r : ShapeClass → Fin n → Fin n)
    (hr : ∀ e i, r e i ≠ i) (M : Moonshine n) :
    SpectralRel (X.withRoute r hr) M ↔ SpectralRel X M :=
  ⟨fun h => ⟨h.1⟩, fun h => ⟨h.1⟩⟩

/-- The laminar condition on two spectra. -/
def Laminar (A B : Set ℕ) : Prop := A ⊆ B ∨ B ⊆ A ∨ Disjoint A B

/-- The RFC's literal coherence condition holds for all pairs of sets. -/
theorem rfc_coherent_tautology (A B : Set ℕ) : A ⊆ B ∨ B ⊆ A ∨ (¬ A ⊆ B ∧ ¬ B ⊆ A) := by
  tauto

/-- Laminar spectra with a common point are comparable. -/
theorem Laminar.comparable {A B : Set ℕ} (h : Laminar A B) {m : ℕ} (hA : m ∈ A) (hB : m ∈ B) :
    A ⊆ B ∨ B ⊆ A := by
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd (Set.disjoint_left.1 h hA) (not_not.2 hB)

end Closet

/-- The closet of an object: spectrally related, pairwise laminar moonshines. -/
structure Closet {n : ℕ} (X : VMSpec n) where
  moonshines : List (Closet.Moonshine n)
  related : ∀ M ∈ moonshines, Closet.SpectralRel X M
  coherent : ∀ M₁ ∈ moonshines, ∀ M₂ ∈ moonshines, Closet.Laminar M₁.spectrum M₂.spectrum

namespace Closet

open SpectrumVM TSP

variable {X : VMSpec n} (C : Closet X)

/-- The objects of the panorama: the moonshines in the closet. -/
def Obj : Type := {M : Moonshine n // M ∈ C.moonshines}

/-- Spectral containment preorders the panorama (so it is a thin category). -/
instance : Preorder C.Obj := Preorder.lift fun M => M.1.spectrum

theorem Obj.le_iff {M₁ M₂ : C.Obj} : M₁ ≤ M₂ ↔ M₁.1.spectrum ⊆ M₂.1.spectrum := Iff.rfl

/-- The panorama's colimit: the union of the spectra. -/
def colimit : Set ℕ := {m | ∃ M ∈ C.moonshines, m ∈ M.spectrum}

/-- The panorama's limit: the intersection of the spectra. -/
def limit : Set ℕ := {m | ∀ M ∈ C.moonshines, m ∈ M.spectrum}

theorem isLUB_colimit : IsLUB {A | ∃ M ∈ C.moonshines, M.spectrum = A} C.colimit := by
  constructor
  · rintro _ ⟨M, hM, rfl⟩ m hm; exact ⟨M, hM, hm⟩
  · intro T hT m ⟨M, hM, hm⟩; exact hT ⟨M, hM, rfl⟩ hm

theorem isGLB_limit : IsGLB {A | ∃ M ∈ C.moonshines, M.spectrum = A} C.limit := by
  constructor
  · rintro _ ⟨M, hM, rfl⟩ m hm; exact hm M hM
  · intro T hT m hm M hM; exact hT ⟨M, hM, rfl⟩ hm

/-- **The colimit lies in the object's carrier** — the global consequence of the per-moonshine
`related` proofs. -/
theorem colimit_subset_carrier : C.colimit ⊆ carrier X := by
  rintro m ⟨M, hM, hm⟩
  exact (C.related M hM).related hm

theorem limit_subset_colimit (h : C.moonshines ≠ []) : C.limit ⊆ C.colimit := by
  obtain ⟨M, hM⟩ := List.exists_mem_of_ne_nil _ h
  intro m hm
  exact ⟨M, hM, hm M hM⟩

theorem limit_subset_carrier (h : C.moonshines ≠ []) : C.limit ⊆ carrier X :=
  (C.limit_subset_colimit h).trans C.colimit_subset_carrier

theorem limit_nil (h : C.moonshines = []) : C.limit = Set.univ := by
  ext m; simp [limit, h]

/-- The empty closet's limit is not inside the carrier (the carrier is finite). -/
theorem limit_nil_not_subset_carrier (h : C.moonshines = []) : ¬ C.limit ⊆ carrier X := by
  rw [C.limit_nil h, Set.univ_subset_iff]
  intro hc
  exact Set.infinite_univ (hc ▸ carrier_finite X)

/-- A nonempty list of pairwise comparable sets has a least element. -/
theorem exists_least_of_comparable :
    ∀ (L : List (Set ℕ)), L ≠ [] → (∀ A ∈ L, ∀ B ∈ L, A ⊆ B ∨ B ⊆ A) →
      ∃ A ∈ L, ∀ B ∈ L, A ⊆ B
  | [], h, _ => absurd rfl h
  | [a], _, _ => ⟨a, by simp, by simp⟩
  | a :: b :: l, _, hc => by
    obtain ⟨m, hm, hmin⟩ := exists_least_of_comparable (b :: l) (by simp)
      (fun A hA B hB => hc A (List.mem_cons_of_mem _ hA) B (List.mem_cons_of_mem _ hB))
    rcases hc a (by simp) m (List.mem_cons_of_mem _ hm) with h | h
    · refine ⟨a, by simp, fun B hB => ?_⟩
      rcases List.mem_cons.1 hB with rfl | hB
      · exact le_rfl
      · exact h.trans (hmin B hB)
    · refine ⟨m, List.mem_cons_of_mem _ hm, fun B hB => ?_⟩
      rcases List.mem_cons.1 hB with rfl | hB
      · exact h
      · exact hmin B hB

/-- **The core moonshine**: in a nonempty closet with nonempty limit, the limit is the spectrum
of one of the closet's moonshines. -/
theorem exists_core (h : C.moonshines ≠ []) (hl : C.limit.Nonempty) :
    ∃ M ∈ C.moonshines, M.spectrum = C.limit := by
  obtain ⟨m, hm⟩ := hl
  obtain ⟨A, hA, hmin⟩ := exists_least_of_comparable (C.moonshines.map Moonshine.spectrum)
    (by simpa using h) (by
      intro A hA B hB
      obtain ⟨M₁, h₁, rfl⟩ := List.mem_map.1 hA
      obtain ⟨M₂, h₂, rfl⟩ := List.mem_map.1 hB
      exact (C.coherent M₁ h₁ M₂ h₂).comparable (hm M₁ h₁) (hm M₂ h₂))
  obtain ⟨M, hM, rfl⟩ := List.mem_map.1 hA
  refine ⟨M, hM, Set.Subset.antisymm (fun x hx M' hM' => ?_) (fun x hx => hx M hM)⟩
  exact hmin _ (List.mem_map_of_mem hM') hx

end Dasein15VM.Closet
