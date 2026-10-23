import RequestProject.Dasein15VM.MonsterWalk.Section
import RequestProject.Dasein15VM.MonsterWalk.Data
import RequestProject.Dasein15VM.MonsterWalk.McKay
import RequestProject.Dasein15VM.MonsterWalk.CharTable

/-!
# REQ-0001 summary theorem

`monster_vm_certified` collects the headline results of the consolidation in one statement,
next to the user's `monster_vm_complete` (which is kept unchanged in `Core.lean`).
-/

namespace MonsterWalkZKP

open Dasein15VM Dasein15

/-- **REQ-0001, certified.**
1. Every certified `VMSpec` trace is a run of its compiled Monster VM program.
2. The Dasein15 walk is a 998-instruction Monster VM program from the initial shard to `finalExp`.
3. It is not a program of increment instructions alone.
4. Every Monster walk has a unique correct (halting) trace.
5. The user's sheaf-section checker accepts an incoherent section.
6. The user's tau table is wrong at `29`.
7. The coefficient of `q` in `j` is `196884 = 47 · 59 · 71 + 1`.
8. The orbifold "proof" is determined by the public statement. -/
theorem monster_vm_certified :
    (∀ {n : ℕ} (S : VMSpec n) (s₀ s : VMState n) (tr : List (VMState n)),
        VMCorrect S s₀ s tr → runOps (compileTrace S tr) s₀.shape = some s.shape) ∧
    (runOps daseinProgram initShape = some finalExp ∧ daseinProgram.length = 998) ∧
    (¬ ∃ w : MonsterWalk, w.initial_state = initShape ∧ w.final = finalExp) ∧
    (∀ w : MonsterWalk, MonsterWalk.Correct w w.trace ∧
        ∀ tr, MonsterWalk.Correct w tr → tr = w.trace) ∧
    ((verifySheafSection section_ex1).valid = true ∧ ¬ ValidSection section_ex1) ∧
    ramanujan_tau 29 ≠ ramanujanTau 29 ∧
    (∀ c : ℕ → ℤ, (∀ i ≤ 2, PowerSeries.coeff i (E4 ^ 3) =
        PowerSeries.coeff i (PowerSeries.mk c * deltaProd 2)) ↔
        c 0 = 1 ∧ c 1 = 744 ∧ c 2 = 196884) ∧
    (∀ x n, orbifoldPS.rel x n → orbifoldPS.prove x n = orbifoldDecode x) :=
  ⟨fun _ _ _ _ h => h.runOps_compile, dasein_is_monster_program, dasein_not_primeProgram,
    fun w => ⟨w.trace_correct, fun _ h => h.unique⟩, verifySheafSection_accepts_incoherent,
    ramanujan_tau_table_wrong.1, mckay_j_coefficients,
    fun x n h => (orbifold_proof_determined x n h).1⟩

end MonsterWalkZKP
