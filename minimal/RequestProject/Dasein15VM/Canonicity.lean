import RequestProject.Dasein15VM.Shape

/-!
# Dasein15 VM, phase 1.2: the three `Eigenspace` definitions do **not** agree

The plan's canonicity theorem asked to show that the eigenspace partitions in `Dasein15.lean`,
`VibeRegister.lean` and `DA51PrefixClassification.lean` coincide, with dimensions 7/5/1/2.
The relevant definitions of the latter two files are transcribed below verbatim (the source files
import large unrelated developments; only `native_decide` proofs were replaced by `decide`).

Findings (all proved):
* Dasein15's partition has class sizes 7/6/2/0 (Earth/Spoke/Hub/Clock), VibeRegister's 7/5/1/2.
* No relabelling of classes turns one index partition into the other, in either direction
  (`not_vibe_factors_dasein`, `not_dasein_factors_vibe`), so the claim is false.
* DA51's prime lists agree exactly with Dasein15's partition (`da51_primes_agree_dasein`);
  DA51's `Eigenspace.dim` values 7/5/1/2 are operator-eigenspace dimensions and coincide with
  VibeRegister's class sizes, not with Dasein15's / DA51's own prime counts (7/6/2).
-/

namespace Dasein15VM.Canonicity

/-! ## VibeRegister (transcribed) -/
namespace Vibe

/-- The four eigenspaces of the SSP vector space. -/
inductive Eigenspace where
  | earth  -- 7D: low primes, dense arithmetic
  | spoke  -- 5D: mid primes, structural bridges
  | hub    -- 1D: prime 47, the entropy gate
  | clock  -- 2D: primes 59, 71, temporal phase
  deriving DecidableEq, Repr, Inhabited

/-- Which eigenspace each SSP index belongs to. -/
def sspEigenspace : Fin 15 → Eigenspace
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ => .earth
  | ⟨7, _⟩ | ⟨8, _⟩ | ⟨9, _⟩ | ⟨10, _⟩ | ⟨11, _⟩ => .spoke
  | ⟨12, _⟩ => .hub
  | ⟨13, _⟩ | ⟨14, _⟩ => .clock

/-- The dimension of each eigenspace. -/
def Eigenspace.dim : Eigenspace → ℕ
  | .earth => 7
  | .spoke => 5
  | .hub   => 1
  | .clock => 2

end Vibe

/-! ## DA51PrefixClassification (transcribed) -/
namespace DA51

/-- The four eigenspaces of operator O = Hub₁₉ · Z₂ in Cl(15,0,0). -/
inductive Eigenspace where
  | earth  -- eigenvalue −1, primes {2,3,5,7,11,13,47}, dim 7
  | spoke  -- eigenvalue −1, mixed from {17,29,31,41,59,71}, dim 5
  | hub    -- eigenvalue +1, direction (e₁₉+e₂₃)/√2, dim 1
  | clock  -- eigenvalue e^{±iπ/3}, 60° rotation plane, dim 2
  deriving DecidableEq, Repr, Inhabited

/-- The dimension of each eigenspace. -/
def Eigenspace.dim : Eigenspace → ℕ
  | .earth => 7
  | .spoke => 5
  | .hub   => 1
  | .clock => 2

/-- Earth primes: {2, 3, 5, 7, 11, 13, 47}. -/
def earthPrimes : List ℕ := [2, 3, 5, 7, 11, 13, 47]

/-- Spoke primes: {17, 29, 31, 41, 59, 71}. -/
def spokePrimes : List ℕ := [17, 29, 31, 41, 59, 71]

/-- Hub primes: {19, 23}. -/
def hubPrimes : List ℕ := [19, 23]

end DA51

open Dasein15

/-- Number of indices in a class. -/
def classSize {α : Type} [DecidableEq α] (a : Fin 15 → α) (e : α) : ℕ :=
  (Finset.univ.filter fun i => a i = e).card

theorem dasein_class_sizes :
    classSize eigenspace .Earth = 7 ∧ classSize eigenspace .Spoke = 6 ∧
      classSize eigenspace .Hub = 2 ∧ classSize eigenspace .Clock = 0 := by decide

theorem vibe_class_sizes :
    classSize Vibe.sspEigenspace .earth = 7 ∧ classSize Vibe.sspEigenspace .spoke = 5 ∧
      classSize Vibe.sspEigenspace .hub = 1 ∧ classSize Vibe.sspEigenspace .clock = 2 := by decide

/-- VibeRegister's class sizes are its declared dimensions. -/
theorem vibe_sizes_eq_dim (e : Vibe.Eigenspace) :
    classSize Vibe.sspEigenspace e = e.dim := by cases e <;> decide

/-- VibeRegister's partition is not a relabelling (or coarsening) of Dasein15's. -/
theorem not_vibe_factors_dasein :
    ¬ ∃ σ : Dasein15.Eigenspace → Vibe.Eigenspace, ∀ i, Vibe.sspEigenspace i = σ (eigenspace i) := by
  rintro ⟨σ, h⟩
  have h0 := h 0
  have h12 := h 12
  simp only [Vibe.sspEigenspace, eigenspace] at h0 h12
  rw [← h0] at h12
  exact absurd h12 (by decide)

/-- Dasein15's partition is not a relabelling (or coarsening) of VibeRegister's. -/
theorem not_dasein_factors_vibe :
    ¬ ∃ σ : Vibe.Eigenspace → Dasein15.Eigenspace, ∀ i, eigenspace i = σ (Vibe.sspEigenspace i) := by
  rintro ⟨σ, h⟩
  have h0 := h 0
  have h6 := h 6
  simp only [Vibe.sspEigenspace, eigenspace] at h0 h6
  rw [← h0] at h6
  exact absurd h6 (by decide)

/-- DA51's prime lists are exactly Dasein15's partition. -/
theorem da51_primes_agree_dasein (i : Fin 15) :
    (SSP i ∈ DA51.earthPrimes ↔ eigenspace i = .Earth) ∧
      (SSP i ∈ DA51.spokePrimes ↔ eigenspace i = .Spoke) ∧
      (SSP i ∈ DA51.hubPrimes ↔ eigenspace i = .Hub) := by
  revert i; decide

/-- **Phase 1.2 canonicity claim, refuted.** It is not the case that the three eigenspace
definitions induce the same partition of the 15 supersingular primes with class sizes 7/5/1/2:
Dasein15's own class sizes are 7/6/2/0 and VibeRegister's partition is not a relabelling of it. -/
theorem eigenspaces_not_canonical :
    ¬ ((∃ σ : Dasein15.Eigenspace → Vibe.Eigenspace,
          ∀ i, Vibe.sspEigenspace i = σ (eigenspace i)) ∧
        classSize eigenspace .Earth = 7 ∧ classSize eigenspace .Spoke = 5 ∧
        classSize eigenspace .Hub = 1 ∧ classSize eigenspace .Clock = 2) :=
  fun h => not_vibe_factors_dasein h.1

end Dasein15VM.Canonicity
