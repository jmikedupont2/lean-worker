import RequestProject.Dasein15VM.MonsterWalk.ZKP
import RequestProject.Dasein15VM.Canonicity

/-!
# Sheaf-section verification: soundness and refutations (REQ-0001 items 2 and 7)

* `verifySheafSection_sound`: the user's checker accepts a section **iff** its prime label is
  supersingular. Three of its four flags are constant `true`; the checker ignores the shard, the
  eigenspace, the Bott phase and the DASL type (`verifySheafSection_ignores`).
  - The orbifold flag being constant is harmless: every shard is the orbifold projection of a
    unique number below `196883` (`shard_realizable`). The Bott flag is guaranteed by the type
    `Fin 8`.
  - The eigenspace flag is not harmless: the checker accepts sections whose eigenspace label
    contradicts the eigenspace of their prime label (`verifySheafSection_accepts_incoherent`).
* `ValidSection` / `checkSection`: the coherent notion — the prime label is supersingular and the
  section's eigenspace is the eigenspace of that prime in the §11 partition
  (`zkpEigenspace`: 7/5/1/2). `checkSection_iff` is its soundness **and** completeness.
* `examples_coherence`: of the six example sections, `section_ex1` (prime `7`, labelled Spoke),
  `section_ex3` (prime `17`, labelled Spoke) and `section_ex4` (prime `23`, labelled Earth) are
  incoherent. `section_ex1` and `section_ex4` are incoherent under Dasein15's partition too
  (`examples_incoherent_dasein`), so "all example sections verify" holds only for the weak
  checker.
* `zkp_partition_eq_vibe`, `zkp_partition_ne_dasein`: the §11 partition is VibeRegister's, not
  Dasein15's.
-/

namespace MonsterWalkZKP

open Dasein15VM

/-! ## The §11 eigenspace partition of the 15 primes -/

/-- §11: Earth `{2,…,17}`, Spoke `{19,23,29,31,41}`, Hub `{47}`, Clock `{59,71}`. -/
def zkpEigenspace : Fin 15 → Eigenspace
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 => .Earth
  | 7 | 8 | 9 | 10 | 11 => .Spoke
  | 12 => .Hub
  | 13 | 14 => .Clock

/-- The class sizes are `earth_dim`, `spoke_dim`, `hub_dim`, `clock_dim`. -/
theorem zkpEigenspace_sizes :
    (Finset.univ.filter fun i => zkpEigenspace i = .Earth).card = earth_dim ∧
    (Finset.univ.filter fun i => zkpEigenspace i = .Spoke).card = spoke_dim ∧
    (Finset.univ.filter fun i => zkpEigenspace i = .Hub).card = hub_dim ∧
    (Finset.univ.filter fun i => zkpEigenspace i = .Clock).card = clock_dim := by decide

/-- Renaming between the eigenspace types. -/
def ofVibe : Canonicity.Vibe.Eigenspace → Eigenspace
  | .earth => .Earth | .spoke => .Spoke | .hub => .Hub | .clock => .Clock

def ofDasein : Dasein15.Eigenspace → Eigenspace
  | .Earth => .Earth | .Spoke => .Spoke | .Hub => .Hub | .Clock => .Clock

/-- The §11 partition is VibeRegister's. -/
theorem zkp_partition_eq_vibe (i : Fin 15) :
    zkpEigenspace i = ofVibe (Canonicity.Vibe.sspEigenspace i) := by
  revert i; decide

/-- The §11 partition is not Dasein15's (e.g. `17` is Earth here and Spoke in Dasein15). -/
theorem zkp_partition_ne_dasein : zkpEigenspace 6 ≠ ofDasein (Dasein15.eigenspace 6) := by
  decide

/-! ## The user's checker -/

/-- **Soundness of `verifySheafSection`, exactly**: it accepts iff the prime label is supersingular. -/
theorem verifySheafSection_sound (s : SheafSection) :
    (verifySheafSection s).valid = true ↔ s.ssp_prime ∈ SSP_list := by
  simp [verifySheafSection, VerificationResult.valid]

/-- The checker depends on the prime label only. -/
theorem verifySheafSection_ignores (s t : SheafSection) (h : s.ssp_prime = t.ssp_prime) :
    (verifySheafSection s).valid = (verifySheafSection t).valid := by
  simp [verifySheafSection, VerificationResult.valid, h]

/-- The hard-coded orbifold flag is justified: every shard is realised by a unique number below
`196883`. -/
theorem shard_realizable (s : SheafSection) :
    ∃! n, n < 196883 ∧ orbifoldProject n = s.orbifold := orbifold_unique_rep _

/-! ## Coherent sections -/

/-- The index of a supersingular prime. -/
def sspIndexOf (p : ℕ) : Option (Fin 15) := (List.finRange 15).find? fun i => SSP_list[i] = p

/-- The §11 eigenspace of a prime (`none` if it is not supersingular). -/
def primeEigenspace (p : ℕ) : Option Eigenspace := (sspIndexOf p).map zkpEigenspace

/-- Dasein15's eigenspace of a prime. -/
def daseinPrimeEigenspace (p : ℕ) : Option Eigenspace :=
  (sspIndexOf p).map fun i => ofDasein (Dasein15.eigenspace i)

/-- A **valid Monster memory cell**: the prime label is supersingular and the eigenspace label is
the §11 eigenspace of that prime. (The shard and Bott phase carry no further constraint:
`shard_realizable`, and `Fin 8`.) -/
def ValidSection (s : SheafSection) : Prop :=
  s.ssp_prime ∈ SSP_list ∧ primeEigenspace s.ssp_prime = some s.eigenspace

/-- The coherent checker. -/
def checkSection (s : SheafSection) : Bool :=
  decide (s.ssp_prime ∈ SSP_list) && primeEigenspace s.ssp_prime == some s.eigenspace

/-- **Soundness and completeness of `checkSection`.** -/
theorem checkSection_iff (s : SheafSection) : checkSection s = true ↔ ValidSection s := by
  simp [checkSection, ValidSection]

/-- A coherent section passes the user's checker. -/
theorem checkSection_verify {s : SheafSection} (h : checkSection s = true) :
    (verifySheafSection s).valid = true :=
  (verifySheafSection_sound s).2 ((checkSection_iff s).1 h).1

/-- Which example sections are coherent. -/
theorem examples_coherence :
    checkSection section_ex1 = false ∧ checkSection section_ex2 = true ∧
    checkSection section_ex3 = false ∧ checkSection section_ex4 = false ∧
    checkSection section_ex5 = true ∧ checkSection section_ex6 = true := by
  decide +kernel

/-- **Refutation**: the user's checker accepts an incoherent section. -/
theorem verifySheafSection_accepts_incoherent :
    (verifySheafSection section_ex1).valid = true ∧ ¬ ValidSection section_ex1 := by
  refine ⟨examples_valid.1, fun h => ?_⟩
  have := (checkSection_iff _).2 h
  rw [examples_coherence.1] at this
  exact absurd this (by decide)

/-- `section_ex1` (prime `7`, Spoke) and `section_ex4` (prime `23`, Earth) are incoherent under
Dasein15's partition as well. -/
theorem examples_incoherent_dasein :
    daseinPrimeEigenspace section_ex1.ssp_prime ≠ some section_ex1.eigenspace ∧
    daseinPrimeEigenspace section_ex4.ssp_prime ≠ some section_ex4.eigenspace := by
  decide +kernel

end MonsterWalkZKP
