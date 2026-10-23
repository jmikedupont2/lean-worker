import RequestProject.Dasein15VM.MonsterWalk.Embed

/-!
# The orbifold projection and the `prove`/`verify` pair (REQ-0001 item 5)

**Orbifold projection (CRT).**
* `orbifoldProject_eq_iff`: two numbers have the same orbifold point iff they agree mod
  `196883 = 71 · 59 · 47`.
* `orbifoldDecode` (explicit CRT idempotents) inverts the projection:
  `orbifoldProject_decode`, `orbifoldDecode_project`; `orbifold_unique_rep`: every orbifold point
  has exactly one representative below `196883`.
* `verify_iff_three_mods`: checking `orbifoldProject n = x` is exactly three modular reductions.

**Proof systems.** `ProofSystem` packages a relation with `prove`/`verify` and the two theorems
*soundness* (an accepted proof implies the statement has a witness) and *completeness* (a witness
yields an accepted proof).
* `orbifoldPS`: statement `x : OrbifoldPoint`, witness `n` with `orbifoldProject n = x`.
* `walkPS S`: statement `(s₀, x)`, witness a trace; it accepts iff the trace is a certified
  `VMSpec` run from `s₀` (via `checkVMTrace`) whose final FRACTRAN number projects to `x`.
  Completeness rests on `checkVMTrace_iff` (the trace checker is complete as well as sound).

**Refutations (no zero-knowledge claim is made).**
* `orbifold_statement_trivial`: every orbifold point has a witness, so a verified `orbifoldPS`
  proof carries no information beyond the point itself.
* `orbifold_proof_determined`: the honest proof is a function of the public statement alone
  (`prove x n = orbifoldDecode x`), and every witness is congruent to it mod `196883`; the
  "DASL address" reveals the witness residue completely, so it is not a zero-knowledge proof.
* `dasein_endpoints_project_zero`: the initial and final FRACTRAN states of the Dasein15 walk both
  project to `(0, 0, 0)` (each is divisible by `47 · 59 · 71`); in particular the initial state
  does not project to the shard `(25, 24, 2)` (`dasein_shard_not_projection`).
-/

namespace MonsterWalkZKP

open Dasein15VM

/-! ## CRT for the orbifold projection -/

theorem natCast_mod_trivector (N : ℕ) {p : ℕ} (hp : p ∣ 196883) :
    ((N % 196883 : ℕ) : ZMod p) = (N : ZMod p) := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_mod_of_dvd _ hp]

/-- Two numbers project to the same orbifold point iff they agree mod `196883`. -/
theorem orbifoldProject_eq_iff (a b : ℕ) :
    orbifoldProject a = orbifoldProject b ↔ a % 196883 = b % 196883 := by
  simp only [orbifoldProject, Prod.mk.injEq, ZMod.natCast_eq_natCast_iff]
  have h1 := Nat.modEq_and_modEq_iff_modEq_mul (a := a) (b := b) (m := 71) (n := 59) (by norm_num)
  have h2 := Nat.modEq_and_modEq_iff_modEq_mul (a := a) (b := b) (m := 71 * 59) (n := 47)
    (by norm_num)
  rw [← and_assoc, h1, h2]
  rfl

/-- CRT reconstruction from the three residues. -/
def orbifoldDecode (x : OrbifoldPoint) : ℕ :=
  (x.1.val * 49914 + x.2.1.val * 113458 + x.2.2.val * 33512) % 196883

theorem orbifoldDecode_lt (x : OrbifoldPoint) : orbifoldDecode x < 196883 :=
  Nat.mod_lt _ (by norm_num)

theorem orbifoldProject_decode (x : OrbifoldPoint) : orbifoldProject (orbifoldDecode x) = x := by
  obtain ⟨a, b, c⟩ := x
  simp only [orbifoldProject, orbifoldDecode, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · rw [natCast_mod_trivector _ (by norm_num)]
    push_cast
    rw [ZMod.natCast_zmod_val, show (49914 : ZMod 71) = 1 by decide,
      show (113458 : ZMod 71) = 0 by decide, show (33512 : ZMod 71) = 0 by decide]
    ring
  · rw [natCast_mod_trivector _ (by norm_num)]
    push_cast
    rw [ZMod.natCast_zmod_val, show (49914 : ZMod 59) = 0 by decide,
      show (113458 : ZMod 59) = 1 by decide, show (33512 : ZMod 59) = 0 by decide]
    ring
  · rw [natCast_mod_trivector _ (by norm_num)]
    push_cast
    rw [ZMod.natCast_zmod_val, show (49914 : ZMod 47) = 0 by decide,
      show (113458 : ZMod 47) = 0 by decide, show (33512 : ZMod 47) = 1 by decide]
    ring

theorem orbifoldDecode_project (n : ℕ) : orbifoldDecode (orbifoldProject n) = n % 196883 := by
  have := (orbifoldProject_eq_iff _ _).1 (orbifoldProject_decode (orbifoldProject n))
  rwa [Nat.mod_eq_of_lt (orbifoldDecode_lt _)] at this

/-- Every orbifold point has exactly one representative below `196883`. -/
theorem orbifold_unique_rep (x : OrbifoldPoint) :
    ∃! n, n < 196883 ∧ orbifoldProject n = x := by
  refine ⟨orbifoldDecode x, ⟨orbifoldDecode_lt x, orbifoldProject_decode x⟩, ?_⟩
  rintro m ⟨hm, rfl⟩
  rw [orbifoldDecode_project, Nat.mod_eq_of_lt hm]

/-- Verification is three modular reductions. -/
theorem verify_iff_three_mods (n : ℕ) (x : OrbifoldPoint) :
    orbifoldProject n = x ↔ n % 71 = x.1.val ∧ n % 59 = x.2.1.val ∧ n % 47 = x.2.2.val := by
  obtain ⟨a, b, c⟩ := x
  simp only [orbifoldProject, Prod.mk.injEq]
  have e : ∀ {p : ℕ} [NeZero p] (y : ZMod p), (n : ZMod p) = y ↔ n % p = y.val := by
    intro p _ y
    constructor
    · rintro rfl; rw [ZMod.val_natCast]
    · intro h; rw [← ZMod.natCast_mod, h, ZMod.natCast_zmod_val]
  rw [e, e, e]

/-- A number divisible by `47 · 59 · 71` projects to the origin. -/
theorem orbifoldProject_eq_zero_of_dvd {n : ℕ} (h : 196883 ∣ n) : orbifoldProject n = 0 := by
  have := (orbifoldProject_eq_iff n 0).2 (by rw [Nat.mod_eq_zero_of_dvd h, Nat.zero_mod])
  rw [this]; simp [orbifoldProject]

/-! ## Proof systems -/

/-- A proof system for a relation, with soundness and completeness. -/
structure ProofSystem (Stmt Wit Pf : Type) where
  /-- The relation: `rel x w` says `w` witnesses the statement `x`. -/
  rel : Stmt → Wit → Prop
  prove : Stmt → Wit → Pf
  verify : Stmt → Pf → Bool
  /-- **Soundness**: an accepted proof implies the statement holds. -/
  sound : ∀ x π, verify x π = true → ∃ w, rel x w
  /-- **Completeness**: a witness yields an accepted proof. -/
  complete : ∀ x w, rel x w → verify x (prove x w) = true

/-- The orbifold proof system: "I know `n` with `orbifoldProject n = x`". The proof is
`n mod 196883`; verification is three modular reductions (`verify_iff_three_mods`). -/
def orbifoldPS : ProofSystem OrbifoldPoint ℕ ℕ where
  rel x n := orbifoldProject n = x
  prove _ n := n % 196883
  verify x π := decide (orbifoldProject π = x)
  sound x π h := ⟨π, of_decide_eq_true h⟩
  complete x n h := by
    simp only [decide_eq_true_eq]
    rw [← h, orbifoldProject_eq_iff, Nat.mod_mod]

/-- **Refutation of informativeness**: every orbifold statement is true. -/
theorem orbifold_statement_trivial (x : OrbifoldPoint) : ∃ n, orbifoldPS.rel x n :=
  ⟨orbifoldDecode x, orbifoldProject_decode x⟩

/-- **Refutation of zero knowledge**: the honest proof is computable from the public statement
alone, and any witness is congruent to it modulo `196883`. -/
theorem orbifold_proof_determined (x : OrbifoldPoint) (n : ℕ) (h : orbifoldPS.rel x n) :
    orbifoldPS.prove x n = orbifoldDecode x ∧ n % 196883 = orbifoldDecode x := by
  change orbifoldProject n = x at h
  subst h
  exact ⟨(orbifoldDecode_project n).symm, (orbifoldDecode_project n).symm⟩

/-! ### Completeness of the `VMSpec` trace checker -/

variable {n : ℕ}

theorem checkChain_complete (S : VMSpec n) :
    ∀ (l : List (VMState n)), (∀ i (h : i + 1 < l.length), step S l[i] = some l[i + 1]) →
      checkChain S l = true
  | [], _ => rfl
  | [_], _ => rfl
  | s :: t :: rest, h => by
    simp only [checkChain, Bool.and_eq_true]
    exact ⟨(checkStep_iff S s t).2 (h 0 (by simp)),
      checkChain_complete S (t :: rest) fun i hi => h (i + 1) (by simp at hi ⊢; omega)⟩

/-- The trace checker is sound **and complete**. -/
theorem checkVMTrace_iff (S : VMSpec n) (s₀ s : VMState n) (tr : List (VMState n)) :
    checkVMTrace S s₀ s tr = true ↔ VMCorrect S s₀ s tr := by
  refine ⟨checkVMTrace_sound S s₀ s tr, fun ⟨h0, h1, h2, h3⟩ => ?_⟩
  simp only [checkVMTrace, Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, checkChain_complete S tr h2⟩, fun x hx => (checkVMInvariant_iff S x).2 (h3 x hx)⟩
  · rw [h0]; exact (stateBEq_iff _ _).2 rfl
  · rw [h1]; exact (stateBEq_iff _ _).2 rfl

/-- The walk proof system for a `VMSpec`: statement `(s₀, x)`; witness and proof a trace; the
verifier replays the trace checker and the orbifold projection of the final FRACTRAN number. -/
def walkPS (S : VMSpec n) : ProofSystem (VMState n × OrbifoldPoint) (List (VMState n))
    (List (VMState n)) where
  rel st tr := ∃ s, VMCorrect S st.1 s tr ∧ orbifoldProject s.config = st.2
  prove _ tr := tr
  verify st tr := match tr.getLast? with
    | some s => checkVMTrace S st.1 s tr && decide (orbifoldProject s.config = st.2)
    | none => false
  sound st tr h := by
    revert h
    cases hl : tr.getLast? with
    | none => simp
    | some s =>
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact fun ⟨h1, h2⟩ => ⟨tr, s, checkVMTrace_sound S _ _ _ h1, h2⟩
  complete st tr := by
    rintro ⟨s, hc, hx⟩
    rw [hc.2.1]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨(checkVMTrace_iff S _ _ _).2 hc, hx⟩

/-! ### The Dasein15 walk -/

/-- The Dasein15 trace is an accepted `walkPS` proof (by completeness, from `dasein_VMCorrect`). -/
theorem dasein_walkPS_accepts :
    (walkPS daseinSpec).verify (s₀, orbifoldProject sFinal.config) daseinTrace = true :=
  (walkPS daseinSpec).complete _ _ ⟨sFinal, dasein_VMCorrect, rfl⟩

/-- **Both endpoints of the Dasein15 walk project to the orbifold origin.** -/
theorem dasein_endpoints_project_zero :
    orbifoldProject s₀.config = 0 ∧ orbifoldProject sFinal.config = 0 := by
  refine ⟨orbifoldProject_eq_zero_of_dvd ?_, orbifoldProject_eq_zero_of_dvd ?_⟩
  · rw [s₀_config]; exact ⟨2 ^ 25 * 3 ^ 24 * 5 ^ 2 * 7 * 11 * 13 * 17 * 19 * 23 * 29 * 31 * 41, by ring⟩
  · rw [sFinal_config]; exact ⟨29 ^ 11 * 31 ^ 48 * 41, by ring⟩

/-- The Dasein15 shard `(25, 24, 2)` is not the orbifold projection of the initial state. -/
theorem dasein_shard_not_projection :
    orbifoldProject s₀.config ≠ ((25 : ZMod 71), (24 : ZMod 59), (2 : ZMod 47)) := by
  rw [dasein_endpoints_project_zero.1]; decide

end MonsterWalkZKP
