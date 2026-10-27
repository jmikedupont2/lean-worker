import RequestProject.Dasein15VM.MonsterWalk.Exec
import RequestProject.Dasein15VM.Walk

/-!
# `VMSpec` inside the Monster VM (REQ-0001 item 4)

* `compileStep` / `compileTrace`: a `Dasein15VM.VMSpec` step moving one unit of exponent from
  `p_i` to `p_j` is the two-instruction Monster program `dec i ; inc j`
  (`step_runOps`). Hence every certified `VMSpec` trace compiles to a Monster VM program with the
  same start and end shapes (`VMCorrect.runOps_compile`), of length `2 · (steps)`
  (`VMCorrect.length_compile`). This is the embedding "`VMSpec` is the permutation-route special
  case of the Monster VM".
* `daseinProgram`: the Dasein15 walk compiled this way: 998 instructions taking the initial shard
  to `finalExp` (`dasein_is_monster_program`).
* **Refutations** of the converse direction and of the literal reading of the handover:
  - `vmStep_not_inc`: no `VMSpec` step (on an invariant state) is a single increment instruction,
    because `VMSpec` steps conserve mass and `inc` raises it by one;
  - `dasein_not_primeProgram`: no `MonsterWalk` (a list of increment instructions, the user's
    `MonsterProgram`) takes the Dasein15 initial shard to the final state: the Dasein15 walk is a
    program of the Monster VM only once decrement instructions are allowed.
-/

namespace MonsterWalkZKP

open Dasein15VM Dasein15

variable {n : ℕ}

theorem firstPos_pos {v : PrimeShape n} {i : Fin n} (h : firstPos v = some i) : 0 < v i := by
  have := List.find?_some h
  simpa using this

/-- The Monster VM program of one `VMSpec` step from state `s`. -/
def compileStep (S : VMSpec n) (s : VMState n) : List (Op n) :=
  match firstPos s.shape with
  | some i => [.dec i, .inc (S.route s.cls i)]
  | none => []

/-- **A `VMSpec` step is a two-instruction Monster program** `dec i ; inc j`. -/
theorem step_runOps {S : VMSpec n} {s s' : VMState n} (h : step S s = some s') :
    runOps (compileStep S s) s.shape = some s'.shape ∧ (compileStep S s).length = 2 := by
  obtain ⟨v, hv, rfl, -⟩ := step_eq_some h
  simp only [routeStep, Option.map_eq_some_iff] at hv
  obtain ⟨i, hi, rfl⟩ := hv
  simp only [compileStep, hi, VMSpec.ofShape]
  exact ⟨runOps_move _ _ (firstPos_pos hi), rfl⟩

/-- The Monster VM program of a trace: the concatenation of its step programs. -/
def compileTrace (S : VMSpec n) : List (VMState n) → List (Op n)
  | s :: t :: rest => compileStep S s ++ compileTrace S (t :: rest)
  | _ => []

theorem compileTrace_chain (S : VMSpec n) :
    ∀ (tr : List (VMState n)) (a b : VMState n), tr.head? = some a → tr.getLast? = some b →
      (∀ i (h : i + 1 < tr.length), step S tr[i] = some tr[i + 1]) →
      runOps (compileTrace S tr) a.shape = some b.shape ∧
        (compileTrace S tr).length = 2 * (tr.length - 1)
  | [], _, _, h0, _, _ => by simp at h0
  | [x], a, b, h0, h1, _ => by
    simp at h0 h1; subst h0; subst h1; simp [compileTrace]
  | x :: y :: rest, a, b, h0, h1, h2 => by
    simp only [List.head?_cons, Option.some.injEq] at h0
    subst h0
    have hs : step S x = some y := h2 0 (by simp)
    obtain ⟨r1, l1⟩ := step_runOps hs
    obtain ⟨r2, l2⟩ := compileTrace_chain S (y :: rest) y b rfl (by simpa using h1)
      (fun i hi => h2 (i + 1) (by simp at hi ⊢; omega))
    refine ⟨?_, ?_⟩
    · rw [compileTrace, runOps_append, r1]; exact r2
    · rw [compileTrace, List.length_append, l1, l2]; simp; omega

/-- **Embedding**: a certified `VMSpec` trace is a Monster VM program run. -/
theorem _root_.Dasein15VM.VMCorrect.runOps_compile {S : VMSpec n} {s₀ s : VMState n} {tr : List (VMState n)}
    (h : VMCorrect S s₀ s tr) : runOps (compileTrace S tr) s₀.shape = some s.shape :=
  (compileTrace_chain S tr s₀ s h.1 h.2.1 h.2.2.1).1

theorem _root_.Dasein15VM.VMCorrect.length_compile {S : VMSpec n} {s₀ s : VMState n} {tr : List (VMState n)}
    (h : VMCorrect S s₀ s tr) : (compileTrace S tr).length = 2 * (tr.length - 1) :=
  (compileTrace_chain S tr s₀ s h.1 h.2.1 h.2.2.1).2

/-- Every instruction of a compiled program is an increment instruction or its inverse (no `nop`). -/
theorem compileTrace_no_nop (S : VMSpec n) : ∀ tr : List (VMState n), Op.nop ∉ compileTrace S tr
  | [] => by simp [compileTrace]
  | [_] => by simp [compileTrace]
  | s :: t :: rest => by
    rw [compileTrace, List.mem_append, not_or]
    refine ⟨?_, compileTrace_no_nop S (t :: rest)⟩
    unfold compileStep; split <;> simp

/-! ## The Dasein15 walk as a Monster VM program -/

/-- The Dasein15 walk, compiled to the Monster VM. -/
def daseinProgram : List MonsterOp := compileTrace daseinSpec daseinTrace

/-- **The Dasein15 walk is a Monster VM program**: 998 instructions (`dec i ; inc (i+1)`
pairs) taking the initial shard to Dasein15's `finalExp`. -/
theorem dasein_is_monster_program :
    runOps daseinProgram initShape = some finalExp ∧ daseinProgram.length = 998 := by
  refine ⟨dasein_VMCorrect.runOps_compile, ?_⟩
  rw [daseinProgram, dasein_VMCorrect.length_compile, daseinTrace_length]

/-! ## Refutations: the Monster walk is not a `VMSpec` walk -/

/-- **No `VMSpec` step is a single increment instruction**: on an invariant state `VMSpec` steps
conserve the mass, while `inc` raises it by one. -/
theorem vmStep_not_inc (S : VMSpec n) {s s' : VMState n} (hs : VMInvariant S s)
    (h : step S s = some s') (i : Fin n) : (Op.inc i).exec s.shape ≠ some s'.shape := by
  intro e
  have m1 := mass_exec_inc i s.shape
  rw [e, Option.map_some, Option.some.injEq] at m1
  have m2 := (step_preserves_invariant S h).2.2
  rw [hs.2.2] at m1
  omega

/-- **The Dasein15 walk is not a `MonsterProgram`**: no list of increment instructions takes the
initial shard to the final state (both have mass 63, and each `inc` adds one to the mass). -/
theorem dasein_not_primeProgram :
    ¬ ∃ w : MonsterWalk, w.initial_state = initShape ∧ w.final = finalExp := by
  rintro ⟨w, h0, h1⟩
  have hm := w.mass_final
  rw [h0, h1] at hm
  have hlen : w.program.length = 0 := by
    have a : mass finalExp = 63 := by decide
    have b : mass initShape = 63 := by decide
    omega
  rw [List.length_eq_zero_iff] at hlen
  have : w.final = w.initial_state := by simp [MonsterWalk.final, hlen]
  rw [h0, h1] at this
  exact absurd (congrFun this 0) (by decide)

end MonsterWalkZKP
