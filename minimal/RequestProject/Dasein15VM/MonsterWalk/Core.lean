import Mathlib

/-!
# `MonsterWalkZKP`, consolidated (REQ-0001 item 1)

This is the user's `MonsterWalkZKP.lean`, with every declaration kept under its original name and
with its original statement. The changes are in proofs: every `native_decide` was replaced
by a kernel-checked proof (`decide`, `decide +kernel`, `rfl` or `norm_num`).

One naming change was made on request: nothing in this file is a Hecke operator, so the
misleading names were replaced. `HeckeInstruction` is now `PrimeInstruction` (raise one prime
exponent by one), the `SheafSection` field `hecke_p` is now `ssp_prime`, and the
`VerificationResult` flag `hecke_valid` is now `prime_valid`. Statements are otherwise unchanged.

What the declarations here mean, and which of them are refuted, is analysed in the sibling
modules of `RequestProject.Dasein15VM.MonsterWalk` (see `MONSTER_WALK_STATUS.md`).
-/

set_option maxHeartbeats 800000

namespace MonsterWalkZKP

/-! ## §1. The 15 SSP Generators of Cl(15,0,0) -/

/-- The 15 supersingular primes, ordered. -/
def SSP_list : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71]

theorem SSP_list_length : SSP_list.length = 15 := rfl

/-- Cl(15,0,0) dimension = 2^15 = 32768. -/
def Cl15_dim : ℕ := 2 ^ 15

theorem Cl15_dim_value : Cl15_dim = 32768 := rfl

/-- The number of blades at each grade k in Cl(15,0,0) = C(15,k). -/
def blades_at_grade (k : ℕ) : ℕ := Nat.choose 15 k

theorem blades_grade_0 : blades_at_grade 0 = 1 := by decide
theorem blades_grade_1 : blades_at_grade 1 = 15 := by decide
theorem blades_grade_2 : blades_at_grade 2 = 105 := by decide +kernel
theorem blades_grade_7 : blades_at_grade 7 = 6435 := by decide +kernel
theorem blades_grade_15 : blades_at_grade 15 = 1 := by decide +kernel

/-- Sum of all blade counts = 2^15. -/
theorem blades_total :
    ((List.range 16).map blades_at_grade).sum = Cl15_dim := by decide +kernel

/-! ## §2. The Exponent Vector -/

/-- An exponent vector over the 15 SSP primes. -/
abbrev ExponentVector := Fin 15 → ℕ

/-- The zero exponent vector (state n = 1, the void). -/
def zeroExponent : ExponentVector := fun _ => 0

/-- The Monster's exponent vector (from |M| factorization). -/
def monsterExponents : ExponentVector := fun i =>
  match i.val with
  | 0  => 46 | 1  => 20 | 2  => 9  | 3  => 6 | 4  => 2 | 5  => 3
  | 6  => 1  | 7  => 1  | 8  => 1  | 9  => 1 | 10 => 1 | 11 => 1
  | 12 => 1  | 13 => 1  | 14 => 1  | _  => 0

/-- The Monster's exponent vector has 15 nonzero components. -/
theorem monster_support_full :
    ∀ i : Fin 15, monsterExponents i > 0 := by decide

/-- The Monster's steepness = max exponent = 46 (at prime 2). -/
theorem monster_steepness : monsterExponents ⟨0, by omega⟩ = 46 := rfl

/-- The Monster's floor = min exponent = 1 (at primes 17–71). -/
theorem monster_floor : monsterExponents ⟨6, by omega⟩ = 1 := rfl

/-! ## §3. The Trivector Gate: 47 × 59 × 71 = 196883 -/

/-- The trivector product. -/
theorem trivector_product : (47 : ℕ) * 59 * 71 = 196883 := by norm_num

/-- McKay: j-coefficient = trivector + 1. -/
theorem mckay_trivector : (47 : ℕ) * 59 * 71 + 1 = 196884 := by norm_num

/-- 47, 59, 71 are pairwise coprime (necessary for CRT). -/
theorem trivector_pairwise_coprime :
    Nat.Coprime 47 59 ∧ Nat.Coprime 47 71 ∧ Nat.Coprime 59 71 := by decide

/-! ## §4. The Orbifold Projection -/

/-- The orbifold torus: Z/71Z × Z/59Z × Z/47Z. -/
abbrev OrbifoldPoint := ZMod 71 × ZMod 59 × ZMod 47

/-- Project a natural number to the orbifold. -/
def orbifoldProject (n : ℕ) : OrbifoldPoint :=
  ((n : ZMod 71), (n : ZMod 59), (n : ZMod 47))

/-! ## §5. Sheaf Sections — VM Memory Cells -/

/-- Eigenspace classification (from Cl(15,0,0) decomposition).
    Earth(7) + Spoke(5) + Hub(1) + Clock(2) = 15. -/
inductive Eigenspace where
  | Earth : Eigenspace
  | Spoke : Eigenspace
  | Hub   : Eigenspace
  | Clock : Eigenspace
  deriving DecidableEq, Repr

theorem eigenspace_decomposition : 7 + 5 + 1 + 2 = 15 := by norm_num

/-- Bott periodicity phase (mod 8). -/
structure BottPhase where
  phase : Fin 8
  deriving DecidableEq, Repr

/-- Bott periodicity labels. -/
def bottLabel (i : Fin 8) : String :=
  match i.val with
  | 0 => "R"  | 1 => "C"  | 2 => "H"  | 3 => "H+H"
  | 4 => "H(2)" | 5 => "C(4)" | 6 => "R(8)" | 7 => "R(8)+R(8)"
  | _ => ""

/-- A sheaf section = a complete VM memory cell. -/
structure SheafSection where
  shard      : Fin 71 × Fin 59 × Fin 47
  encoding   : String
  eigenspace : Eigenspace
  bott       : BottPhase
  ssp_prime    : ℕ
  dasl_type  : Fin 8
  deriving Repr

/-- The orbifold of a sheaf section. -/
def SheafSection.orbifold (s : SheafSection) : OrbifoldPoint :=
  ((s.shard.1 : ZMod 71), (s.shard.2.1 : ZMod 59), (s.shard.2.2 : ZMod 47))

/-! ## §6. The DASL Certificate Chain -/

/-- A DASL certificate = a chain of sheaf sections. -/
structure DASLCertificate where
  sections : List SheafSection
  nonempty : sections.length > 0
  deriving Repr

/-- The orbifold trace of a certificate. -/
def DASLCertificate.orbifoldTrace (c : DASLCertificate) : List OrbifoldPoint :=
  c.sections.map SheafSection.orbifold

/-- 0xDA51 prefix = 55889 decimal. -/
def DA51_PREFIX : ℕ := 0xDA51

theorem da51_prefix_value : DA51_PREFIX = 55889 := rfl

/-! ## §7. The 194 Irreps as Data Types -/

/-- Monster conjugacy class count = opcode count. -/
def num_opcodes : ℕ := 194

/-- Number of distinct Thompson series = distinct opcode signatures. -/
def num_signatures : ℕ := 171

/-- Number of "vacuum sheet" irreps (v_2 = v_3 = 0). -/
def vacuum_sheet_size : ℕ := 19

/-- 194 - 171 = 23 shared series = 23 umbral shadow classes. -/
theorem shared_opcodes : num_opcodes - num_signatures = 23 := by decide

/-- Smallest Monster irrep dimensions. -/
def irrepDim : ℕ → ℕ
  | 0 => 1       | 1 => 196883
  | 2 => 21296876 | 3 => 842609326
  | _ => 0

/-- The trivial rep dimension is 1 (the autoencoder bottleneck). -/
theorem trivial_rep_dim : irrepDim 0 = 1 := rfl

/-- The minimal faithful rep is the trivector volume. -/
theorem minimal_faithful_is_trivector : irrepDim 1 = 47 * 59 * 71 := rfl

/-- Each irrep expands 1 unit into dim(rho_i) voxels. -/
theorem voxel_expansion : irrepDim 1 = 196883 := rfl

/-! ## §8. Prime-Increment Instructions -/

/-- A prime-increment instruction: raise the exponent of one SSP prime `p` by one
(multiply the Gödel number by `p`). Called `HeckeInstruction` in the original file; renamed
because it is not a Hecke operator. -/
structure PrimeInstruction where
  prime_index : Fin 15
  deriving DecidableEq, Repr

/-- The SSP prime associated with an increment instruction. -/
def PrimeInstruction.prime (h : PrimeInstruction) : ℕ :=
  SSP_list[h.prime_index]

/-- A Monster Walk program = sequence of increment instructions. -/
abbrev MonsterProgram := List PrimeInstruction

/-- A Monster Walk = initial state + program. -/
structure MonsterWalk where
  initial_state : ExponentVector
  program       : MonsterProgram
  deriving Repr

/-! ## §9. Ramanujan Tau Function (the user's table; see `Tau.lean` for its audit) -/

/-- Ramanujan tau(p) for the 15 SSP primes (as given in `MonsterWalkZKP.lean`). -/
def ramanujan_tau : ℕ → ℤ
  | 2  => -24         | 3  => 252
  | 5  => 4830        | 7  => -16744
  | 11 => 534612      | 13 => -577738
  | 17 => -6905934    | 19 => 10661420
  | 23 => 18643272    | 29 => -128406630
  | 31 => 52843168    | 41 => -308120442
  | 47 => 2687348496  | 59 => 7335488382
  | 71 => -5765995416 | _  => 0

/-- tau(2) = -24, so tau(2) mod 24 = 0. -/
theorem tau_2_mod24 : ramanujan_tau 2 % 24 = 0 := by decide

/-- tau(23) mod 24 = 0. -/
theorem tau_23_mod24 : ramanujan_tau 23 % 24 = 0 := by decide

/-- tau(47) mod 24 = 0. -/
theorem tau_47_mod24 : ramanujan_tau 47 % 24 = 0 := by decide

/-- tau(71) mod 24 = 0. -/
theorem tau_71_mod24 : ramanujan_tau 71 % 24 = 0 := by decide

/-- tau(29) mod 24 = 18 (does NOT satisfy tadpole condition). -/
theorem tau_29_mod24 : ramanujan_tau 29 % 24 = 18 := by decide

/-- Ramanujan congruence: tau(p) mod p = 0 for p in {2,3,5,7}. -/
theorem ramanujan_congruence_2 : ramanujan_tau 2 % 2 = 0 := by decide
theorem ramanujan_congruence_3 : ramanujan_tau 3 % 3 = 0 := by decide
theorem ramanujan_congruence_5 : ramanujan_tau 5 % 5 = 0 := by decide
theorem ramanujan_congruence_7 : ramanujan_tau 7 % 7 = 0 := by decide

/-- SSP primes where tau(p) mod 24 = 0: {2, 23, 47, 71}. -/
theorem tau_zero_mod24_primes :
    ramanujan_tau 2 % 24 = 0 ∧
    ramanujan_tau 23 % 24 = 0 ∧
    ramanujan_tau 47 % 24 = 0 ∧
    ramanujan_tau 71 % 24 = 0 :=
  ⟨tau_2_mod24, tau_23_mod24, tau_47_mod24, tau_71_mod24⟩

/-! ## §10. The Monster-Matching Score -/

/-- Monster matching score components. -/
structure MonsterScore where
  support : ℕ
  floor   : ℕ
  steep   : ℕ
  deriving DecidableEq, Repr

/-- The Monster's own score: perfect match (15/15 support). -/
def monsterSelfScore : MonsterScore where
  support := 15; floor := 1; steep := 46

/-- Baby Monster score (11/15 support). -/
def babyMonsterScore : MonsterScore where
  support := 11; floor := 1; steep := 41

/-- Fi24' score (9/15 support). -/
def fi24Score : MonsterScore where
  support := 9; floor := 1; steep := 21

theorem monster_full_support : monsterSelfScore.support = 15 := rfl
theorem baby_partial_support : babyMonsterScore.support = 11 := rfl

/-! ## §11. The Eigenspace Decomposition: 15 = 7 + 5 + 1 + 2 -/

def earth_dim : ℕ := 7
def spoke_dim : ℕ := 5
def hub_dim   : ℕ := 1
def clock_dim : ℕ := 2

theorem eigenspace_sum : earth_dim + spoke_dim + hub_dim + clock_dim = 15 := by decide

/-! ## §12. Shadow Cone — Missing Weights -/

/-- Number of minimal shadows (extremal rays of the shadow cone). -/
def num_minimal_shadows : ℕ := 890

/-- The champion shadow: irrep[13] tensor irrep[28], hitting v_2=8, v_5=4. -/
def champion_shadow : ExponentVector := fun i =>
  match i.val with
  | 0  => 8  | 1  => 0  | 2  => 4  | 3  => 1 | 4  => 1 | 5  => 3
  | 6  => 0  | 7  => 2  | 8  => 2  | 9  => 1 | 10 => 2 | 11 => 2
  | 12 => 2  | 13 => 2  | 14 => 2  | _  => 0

/-- The champion has gaps at positions 1 (prime 3) and 6 (prime 17). -/
theorem champion_gaps :
    champion_shadow ⟨1, by omega⟩ = 0 ∧
    champion_shadow ⟨6, by omega⟩ = 0 := by decide

/-! ## §13. ZKP Verification Protocol -/

/-- A ZKP verification result. -/
structure VerificationResult where
  orbifold_valid   : Bool
  eigenspace_valid : Bool
  bott_valid       : Bool
  prime_valid      : Bool
  deriving DecidableEq, Repr

/-- A section is valid iff all checks pass. -/
def VerificationResult.valid (v : VerificationResult) : Bool :=
  v.orbifold_valid && v.eigenspace_valid && v.bott_valid && v.prime_valid

/-- Verify a sheaf section (basic structural checks). -/
def verifySheafSection (s : SheafSection) : VerificationResult where
  orbifold_valid   := true
  eigenspace_valid := true
  bott_valid       := true
  prime_valid      := decide (s.ssp_prime ∈ SSP_list)

/-! ## §14. Example Sheaf Sections (from VM trace) -/

/-- shard (11, 49, 29), Spoke, Bott=C, prime 7 -/
def section_ex1 : SheafSection where
  shard := (⟨11, by omega⟩, ⟨49, by omega⟩, ⟨29, by omega⟩)
  encoding := "raw"; eigenspace := .Spoke
  bott := ⟨⟨1, by omega⟩⟩; ssp_prime := 7; dasl_type := ⟨1, by omega⟩

/-- shard (20, 35, 11), Earth, Bott=R(8), prime 13 -/
def section_ex2 : SheafSection where
  shard := (⟨20, by omega⟩, ⟨35, by omega⟩, ⟨11, by omega⟩)
  encoding := "raw"; eigenspace := .Earth
  bott := ⟨⟨6, by omega⟩⟩; ssp_prime := 13; dasl_type := ⟨3, by omega⟩

/-- shard (63, 43, 26), Spoke, Bott=C(4), prime 17 -/
def section_ex3 : SheafSection where
  shard := (⟨63, by omega⟩, ⟨43, by omega⟩, ⟨26, by omega⟩)
  encoding := "raw"; eigenspace := .Spoke
  bott := ⟨⟨5, by omega⟩⟩; ssp_prime := 17; dasl_type := ⟨3, by omega⟩

/-- shard (55, 50, 41), Earth, Bott=R, prime 23 -/
def section_ex4 : SheafSection where
  shard := (⟨55, by omega⟩, ⟨50, by omega⟩, ⟨41, by omega⟩)
  encoding := "raw"; eigenspace := .Earth
  bott := ⟨⟨0, by omega⟩⟩; ssp_prime := 23; dasl_type := ⟨1, by omega⟩

/-- shard (23, 46, 22), Spoke, Bott=H(2), prime 31 -/
def section_ex5 : SheafSection where
  shard := (⟨23, by omega⟩, ⟨46, by omega⟩, ⟨22, by omega⟩)
  encoding := "raw"; eigenspace := .Spoke
  bott := ⟨⟨4, by omega⟩⟩; ssp_prime := 31; dasl_type := ⟨1, by omega⟩

/-- shard (0, 37, 1), Earth, Bott=H+H, prime 3 — near void -/
def section_ex6 : SheafSection where
  shard := (⟨0, by omega⟩, ⟨37, by omega⟩, ⟨1, by omega⟩)
  encoding := "raw"; eigenspace := .Earth
  bott := ⟨⟨3, by omega⟩⟩; ssp_prime := 3; dasl_type := ⟨6, by omega⟩

/-- All example sections verify. -/
theorem examples_valid :
    (verifySheafSection section_ex1).valid = true ∧
    (verifySheafSection section_ex2).valid = true ∧
    (verifySheafSection section_ex3).valid = true ∧
    (verifySheafSection section_ex4).valid = true ∧
    (verifySheafSection section_ex5).valid = true ∧
    (verifySheafSection section_ex6).valid = true := by
  simp only [verifySheafSection, VerificationResult.valid, section_ex1, section_ex2,
             section_ex3, section_ex4, section_ex5, section_ex6, SSP_list]
  decide

/-! ## §15. Master Theorem: The Monster IS the VM -/

/-- The Monster VM is complete. -/
theorem monster_vm_complete :
    Cl15_dim = 32768 ∧
    SSP_list.length = 15 ∧
    (47 : ℕ) * 59 * 71 = 196883 ∧
    (47 : ℕ) * 59 * 71 + 1 = 196884 ∧
    num_opcodes = 194 ∧
    num_signatures = 171 ∧
    num_opcodes - num_signatures = 23 ∧
    earth_dim + spoke_dim + hub_dim + clock_dim = 15 ∧
    monsterSelfScore.support = 15 ∧
    irrepDim 0 = 1 ∧
    irrepDim 1 = 196883 := by
  refine ⟨rfl, rfl, by norm_num, by norm_num,
          rfl, rfl, by decide, by decide, rfl, rfl, rfl⟩

end MonsterWalkZKP
