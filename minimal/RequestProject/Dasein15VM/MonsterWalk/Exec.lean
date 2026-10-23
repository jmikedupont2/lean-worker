import RequestProject.Dasein15VM.MonsterWalk.Core
import RequestProject.Dasein15VM.VM

/-!
# Execution semantics for the Monster VM (REQ-0001 item 2)

`MonsterWalkZKP` gives `MonsterWalk` (initial exponent vector + list of increment instructions) but no
execution semantics. This file supplies one.

* **Instruction set** `Op n` over an exponent vector `PrimeShape n`:
  - `inc i` (a `PrimeInstruction` for `p = p_i`): multiply the FRACTRAN state by `p_i`, i.e. raise
    exponent `i` by one;
  - `dec i`: divide by `p_i`, i.e. lower exponent `i` by one; it **faults** (`none`) when the
    exponent is `0`;
  - `nop`: identity.
  The semantics is checked against the Gödel number: `godel_exec_inc`, `godel_exec_dec`.
  These are register increments/decrements of a FRACTRAN/Minsky machine, not Hecke operators.
  (The original `MonsterWalkZKP` called the increment "apply `T_p`"; that name was dropped.)
* `MonsterWalk.step : MonsterWalk → Option MonsterWalk` pops and executes one increment instruction;
  `none` means *halt* (empty program).
* `MonsterWalk.Correct w tr`: the trace-indexed correctness predicate (analogue of `VMCorrect`),
  its `Bool` checker `checkMonsterTrace`, soundness `checkMonsterTrace_sound`, existence
  (`MonsterWalk.trace_correct`), uniqueness (`MonsterWalk.Correct.unique`) and kernel `Evidence`.
* `MonsterWalk.godel_final`: running an increment program multiplies the Gödel number by the product of
  the program's primes; `MonsterWalk.mass_final`: it adds the program length to the mass.
* `nop_ne_halt`: the `nop` instruction never halts, while halting is the empty program — so
  "NOP" and "halt" are different behaviours in this semantics.
-/

namespace MonsterWalkZKP

open Dasein15VM
open SpectrumVM (Evidence VerificationClaim)

variable {n : ℕ}

/-! ## The instruction set -/

/-- Monster VM instructions over an `n`-prime exponent vector. -/
inductive Op (n : ℕ) where
  /-- Increment register `i`: multiply the state by `p_i`. -/
  | inc (i : Fin n)
  /-- Decrement register `i`: divide the state by `p_i` (faults if `p_i` does not divide it). -/
  | dec (i : Fin n)
  /-- Identity. -/
  | nop
  deriving DecidableEq, Repr

/-- The 15-prime instruction set. -/
abbrev MonsterOp := Op 15

/-- Execute one instruction (`none` = fault). -/
def Op.exec : Op n → PrimeShape n → Option (PrimeShape n)
  | .inc i, v => some (Function.update v i (v i + 1))
  | .dec i, v => if 0 < v i then some (Function.update v i (v i - 1)) else none
  | .nop, v => some v

/-- Execute a program (`none` = some instruction faulted). -/
def runOps : List (Op n) → PrimeShape n → Option (PrimeShape n)
  | [], v => some v
  | o :: os, v => (o.exec v).bind (runOps os)

@[simp] theorem runOps_nil (v : PrimeShape n) : runOps [] v = some v := rfl

theorem runOps_cons (o : Op n) (os : List (Op n)) (v : PrimeShape n) :
    runOps (o :: os) v = (o.exec v).bind (runOps os) := rfl

theorem runOps_append (p q : List (Op n)) (v : PrimeShape n) :
    runOps (p ++ q) v = (runOps p v).bind (runOps q) := by
  induction p generalizing v with
  | nil => rfl
  | cons o os ih =>
    simp only [List.cons_append, runOps_cons]
    cases o.exec v <;> simp [ih]

/-- `nop` is the identity instruction. -/
@[simp] theorem exec_nop (v : PrimeShape n) : (Op.nop : Op n).exec v = some v := rfl

/-- `inc` multiplies the Gödel number by `p`. -/
theorem godel_exec_inc (B : PrimeBasis n) (i : Fin n) (v : PrimeShape n) :
    ((Op.inc i).exec v).map (godel B) = some (godel B v * B.p i) := by
  simp only [Op.exec, Option.map_some, Option.some.injEq, godel_eq_prod]
  have := prod_update_mul B v i (v i + 1)
  rw [pow_succ] at this
  exact Nat.eq_of_mul_eq_mul_right (pow_pos (B.prime i).pos (v i)) (by rw [this]; ring)

/-- `dec` succeeds iff `p` divides the Gödel number, and then divides it by `p`. -/
theorem godel_exec_dec (B : PrimeBasis n) (i : Fin n) (v : PrimeShape n) :
    ((Op.dec i).exec v).map (godel B) =
      if B.p i ∣ godel B v then some (godel B v / B.p i) else none := by
  by_cases h : 0 < v i
  · rw [if_pos ((dvd_godel_iff B v i).2 h)]
    simp only [Op.exec, if_pos h, Option.map_some, Option.some.injEq]
    have hk := prod_update_mul B v i (v i - 1)
    rw [← godel_eq_prod, ← godel_eq_prod] at hk
    obtain ⟨m, hm⟩ : ∃ m, v i = m + 1 := ⟨v i - 1, by omega⟩
    have e : godel B (Function.update v i (v i - 1)) * B.p i = godel B v := by
      rw [hm, Nat.add_sub_cancel, pow_succ] at hk
      apply Nat.eq_of_mul_eq_mul_right (pow_pos (B.prime i).pos m)
      rw [hm, Nat.add_sub_cancel]
      calc _ = godel B (Function.update v i m) * (B.p i ^ m * B.p i) := by ring
        _ = _ := hk
    rw [← e, Nat.mul_div_cancel _ (B.prime i).pos]
  · rw [if_neg (fun hd => h ((dvd_godel_iff B v i).1 hd))]
    simp [Op.exec, h]

/-- `inc` adds one to the mass. -/
theorem mass_exec_inc (i : Fin n) (v : PrimeShape n) :
    ((Op.inc i).exec v).map mass = some (mass v + 1) := by
  simp only [Op.exec, Option.map_some, Option.some.injEq, mass_eq_sum]
  have := sum_update_add v i (v i + 1)
  omega

/-- `dec` removes one from the mass when it succeeds. -/
theorem mass_exec_dec {i : Fin n} {v w : PrimeShape n}
    (h : (Op.dec i).exec v = some w) : mass w + 1 = mass v := by
  simp only [Op.exec] at h
  split_ifs at h with hv
  cases h
  simp only [mass_eq_sum]
  have := sum_update_add v i (v i - 1)
  omega

/-- A Dasein15-style move (one unit of exponent from `i` to `j`) is `dec i` then `inc j`. -/
theorem runOps_move (v : PrimeShape n) {i : Fin n} (j : Fin n) (h : 0 < v i) :
    runOps [.dec i, .inc j] v = some (moveUnit v i j) := by
  simp [runOps, Op.exec, h, moveUnit]

/-! ## Increment programs: `MonsterWalk.step` -/

/-- An increment instruction as an instruction of the Monster VM. -/
def PrimeInstruction.toOp (h : PrimeInstruction) : MonsterOp := .inc h.prime_index

/-- Apply one increment instruction to an exponent vector. -/
def PrimeInstruction.apply (h : PrimeInstruction) (v : ExponentVector) : ExponentVector :=
  Function.update v h.prime_index (v h.prime_index + 1)

theorem PrimeInstruction.exec_toOp (h : PrimeInstruction) (v : ExponentVector) :
    h.toOp.exec v = some (h.apply v) := rfl

/-- **One step of a Monster walk**: execute the first instruction; `none` = halt. -/
def MonsterWalk.step (w : MonsterWalk) : Option MonsterWalk :=
  match w.program with
  | [] => none
  | h :: rest => some ⟨h.apply w.initial_state, rest⟩

/-- A walk halts exactly when its program is empty. -/
theorem MonsterWalk.step_eq_none_iff (w : MonsterWalk) : w.step = none ↔ w.program = [] := by
  unfold MonsterWalk.step
  split <;> simp_all

/-- **NOP ≠ halt**: `nop` always continues, while `step` halts only on an empty program. -/
theorem nop_ne_halt (v : ExponentVector) :
    (Op.nop : MonsterOp).exec v ≠ none ∧
      ∀ w : MonsterWalk, w.step = none ↔ w.program = [] :=
  ⟨by simp, MonsterWalk.step_eq_none_iff⟩

/-- The final exponent vector of a walk. -/
def MonsterWalk.final (w : MonsterWalk) : ExponentVector :=
  w.program.foldl (fun v h => h.apply v) w.initial_state

/-- The program of a walk, as Monster VM instructions. -/
def MonsterWalk.ops (w : MonsterWalk) : List MonsterOp := w.program.map PrimeInstruction.toOp

theorem MonsterWalk.runOps_ops (w : MonsterWalk) : runOps w.ops w.initial_state = some w.final := by
  obtain ⟨v, p⟩ := w
  simp only [MonsterWalk.ops, MonsterWalk.final]
  induction p generalizing v with
  | nil => rfl
  | cons h p ih => simp [runOps, PrimeInstruction.exec_toOp, ih]

/-- **Gödel semantics of increment programs**: the final FRACTRAN state is the initial one times the
product of the program's primes. -/
theorem MonsterWalk.godel_final (B : PrimeBasis 15) (w : MonsterWalk) :
    godel B w.final = godel B w.initial_state * (w.program.map fun h => B.p h.prime_index).prod := by
  obtain ⟨v, p⟩ := w
  simp only [MonsterWalk.final]
  induction p generalizing v with
  | nil => simp
  | cons h p ih =>
    have e := godel_exec_inc B h.prime_index v
    simp only [Op.exec, Option.map_some, Option.some.injEq] at e
    simp only [List.foldl_cons, List.map_cons, List.prod_cons]
    rw [ih, PrimeInstruction.apply, e]; ring

/-- **Mass semantics of increment programs**: each instruction adds one to the mass. -/
theorem MonsterWalk.mass_final (w : MonsterWalk) :
    mass w.final = mass w.initial_state + w.program.length := by
  obtain ⟨v, p⟩ := w
  simp only [MonsterWalk.final]
  induction p generalizing v with
  | nil => simp
  | cons h p ih =>
    have e := mass_exec_inc h.prime_index v
    simp only [Op.exec, Option.map_some, Option.some.injEq] at e
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, PrimeInstruction.apply, e]; ring

/-! ## Trace correctness for Monster walks -/

/-- **Monster walk correctness**: `tr` starts at `w`, each consecutive pair is a `step`, and the
last walk has halted. -/
def MonsterWalk.Correct (w : MonsterWalk) (tr : List MonsterWalk) : Prop :=
  tr.head? = some w ∧ (∀ i (h : i + 1 < tr.length), tr[i].step = some tr[i + 1]) ∧
    ∃ z, tr.getLast? = some z ∧ z.step = none

/-- Boolean equality of walks. -/
def walkBEq (a b : MonsterWalk) : Bool :=
  shapeBEq a.initial_state b.initial_state && a.program == b.program

theorem walkBEq_iff (a b : MonsterWalk) : walkBEq a b = true ↔ a = b := by
  obtain ⟨v, p⟩ := a; obtain ⟨u, q⟩ := b
  simp [walkBEq, shapeBEq_iff]

/-- `Bool` check that consecutive walks are steps. -/
def checkWalkChain : List MonsterWalk → Bool
  | a :: b :: rest => (match a.step with | some c => walkBEq c b | none => false) &&
      checkWalkChain (b :: rest)
  | _ => true

theorem checkWalkChain_sound :
    ∀ (l : List MonsterWalk), checkWalkChain l = true →
      ∀ i (h : i + 1 < l.length), l[i].step = some l[i + 1]
  | [], _, i, h => by simp at h
  | [_], _, i, h => by simp at h
  | a :: b :: rest, hc, i, h => by
    simp only [checkWalkChain, Bool.and_eq_true] at hc
    rcases i with _ | i
    · have h1 := hc.1
      cases hs : a.step with
      | none => rw [hs] at h1; simp at h1
      | some c => rw [hs] at h1; simp only [walkBEq_iff] at h1; show a.step = some b; rw [hs, h1]
    · exact checkWalkChain_sound (b :: rest) hc.2 i (by simp at h ⊢; omega)

/-- The trace checker. -/
def checkMonsterTrace (w : MonsterWalk) (tr : List MonsterWalk) : Bool :=
  (match tr.head? with | some a => walkBEq a w | none => false) && checkWalkChain tr &&
    (match tr.getLast? with | some z => z.program.isEmpty | none => false)

/-- **Trace checker soundness.** -/
theorem checkMonsterTrace_sound (w : MonsterWalk) (tr : List MonsterWalk)
    (h : checkMonsterTrace w tr = true) : MonsterWalk.Correct w tr := by
  simp only [checkMonsterTrace, Bool.and_eq_true] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  refine ⟨?_, checkWalkChain_sound tr h1, ?_⟩
  · revert h0; cases tr.head? <;> simp [walkBEq_iff]
  · revert h2; cases tr.getLast? with
    | none => simp
    | some z => simp [MonsterWalk.step_eq_none_iff]

/-- The trace generated by running from `v` the program `p`. -/
def traceFrom : ExponentVector → MonsterProgram → List MonsterWalk
  | v, [] => [⟨v, []⟩]
  | v, h :: rest => ⟨v, h :: rest⟩ :: traceFrom (h.apply v) rest

/-- The trace generated by running a walk to completion. -/
def MonsterWalk.trace (w : MonsterWalk) : List MonsterWalk := traceFrom w.initial_state w.program

theorem traceFrom_ne_nil (v : ExponentVector) (p : MonsterProgram) : traceFrom v p ≠ [] := by
  cases p <;> simp [traceFrom]

theorem traceFrom_getElem_zero (v : ExponentVector) (p : MonsterProgram)
    (h : 0 < (traceFrom v p).length) : (traceFrom v p)[0] = ⟨v, p⟩ := by
  cases p <;> rfl

theorem traceFrom_head (v : ExponentVector) (p : MonsterProgram) :
    (traceFrom v p).head? = some ⟨v, p⟩ := by
  cases p <;> rfl

theorem traceFrom_getLast (v : ExponentVector) (p : MonsterProgram) :
    (traceFrom v p).getLast? = some ⟨p.foldl (fun v h => h.apply v) v, []⟩ := by
  induction p generalizing v with
  | nil => rfl
  | cons h p ih =>
    rw [traceFrom, List.getLast?_cons, ih]; rfl

theorem traceFrom_chain (v : ExponentVector) (p : MonsterProgram) :
    ∀ i (h : i + 1 < (traceFrom v p).length),
      (traceFrom v p)[i].step = some (traceFrom v p)[i + 1] := by
  induction p generalizing v with
  | nil => intro i h; simp [traceFrom] at h
  | cons hd p ih =>
    intro i hi
    rcases i with _ | i
    · simp only [traceFrom, List.getElem_cons_zero, List.getElem_cons_succ]
      rw [traceFrom_getElem_zero]; rfl
    · simp only [traceFrom, List.getElem_cons_succ]
      exact ih _ i (by simpa [traceFrom] using hi)

theorem MonsterWalk.trace_head (w : MonsterWalk) : w.trace.head? = some w := traceFrom_head _ _

/-- The last walk of the generated trace carries the final exponent vector. -/
theorem MonsterWalk.trace_getLast (w : MonsterWalk) :
    w.trace.getLast? = some ⟨w.final, []⟩ := traceFrom_getLast _ _

/-- **Existence**: the generated trace is correct (every walk terminates). -/
theorem MonsterWalk.trace_correct (w : MonsterWalk) : MonsterWalk.Correct w w.trace :=
  ⟨w.trace_head, traceFrom_chain _ _, _, w.trace_getLast, rfl⟩

/-- **Uniqueness**: a correct trace is the generated one. -/
theorem MonsterWalk.Correct.unique {w : MonsterWalk} {tr : List MonsterWalk}
    (h : MonsterWalk.Correct w tr) : tr = w.trace := by
  obtain ⟨v, p⟩ := w
  simp only [MonsterWalk.trace]
  induction p generalizing v tr with
  | nil =>
    obtain ⟨h0, h1, z, hz, hzs⟩ := h
    rcases tr with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · simp at h0
    · simp at h0; subst h0; rfl
    · simp at h0; subst h0
      have := h1 0 (by simp)
      simp [MonsterWalk.step] at this
  | cons hd p ih =>
    obtain ⟨h0, h1, z, hz, hzs⟩ := h
    rcases tr with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · simp at h0
    · simp at h0 hz; subst h0; subst hz; simp [MonsterWalk.step] at hzs
    · simp at h0; subst h0
      have hb : b = ⟨hd.apply v, p⟩ := by
        have := h1 0 (by simp)
        simp [MonsterWalk.step] at this; exact this.symm
      subst hb
      have := ih (hd.apply v) (tr := ⟨hd.apply v, p⟩ :: rest)
        ⟨rfl, fun i hi => h1 (i + 1) (by simp at hi ⊢; omega), z,
          by simpa [List.getLast?_cons] using hz, hzs⟩
      rw [traceFrom, ← this]

/-- Kernel evidence for Monster walk correctness from a closed proof of the checker. -/
def monsterTraceEvidence (w : MonsterWalk) (tr : List MonsterWalk)
    (h : checkMonsterTrace w tr = true) (claim : VerificationClaim) :
    Evidence (MonsterWalk.Correct w tr) :=
  .kernel (checkMonsterTrace_sound w tr h) claim

/-- Example: from the void, `inc 2; inc 3; inc 71` reaches the state `2 · 3 · 71 = 426`. -/
def exampleWalk : MonsterWalk := ⟨zeroExponent, [⟨0⟩, ⟨1⟩, ⟨14⟩]⟩

theorem exampleWalk_checked : checkMonsterTrace exampleWalk exampleWalk.trace = true := by
  decide +kernel

theorem exampleWalk_godel : godel sspBasis exampleWalk.final = 426 := by decide +kernel

end MonsterWalkZKP
