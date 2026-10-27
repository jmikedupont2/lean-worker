import RequestProject.Dasein15VM.Irreps.Table
import RequestProject.Dasein15VM.MonsterWalk.Exec
import RequestProject.Dasein15VM.Walk

/-!
# Visiting every irreducible representation of the Monster

**Which machine can do it.**

* The Dasein15 VM (any `VMSpec`) conserves mass, so one certified trace only meets irreducible
  representations of a single mass. The table has 41 different masses and at most 17 rows share a
  mass (`vm_trace_irreps_le`). The Dasein15 walk itself runs at mass 63, above the largest
  mass 56 of any row, so it meets **no** irreducible representation (`dasein_trace_no_irrep`).
* A program of increment instructions `inc` only (multiply by `p`) can only raise exponents, so the
  states it passes through form a chain; rows 1 and 2 (`196883 = 47·59·71` and
  `21296876 = 2²·31·41·59·71`) are incomparable, so no such program visits all of them
  (`no_inc_only_tour`).
* The Monster VM with `inc` **and** `dec` (the grow and shrink transitions) can.

**The tour.** `moveProg u w` is the straight-line program that, for each prime, applies `dec`
`u_p - w_p` times and `inc` `w_p - u_p` times; `runOps_moveProg` proves it takes `u` to `w` without
faulting. `tourProg v₀ ts` chains these through a list of target shapes, and `tourProg_visits` says
the run passes through every target (`Visits`: some prefix of the program ends there).

`irrepProg` is the tour that starts at the trivial representation (FRACTRAN state `1`), visits the
170 distinct exponent vectors in the order `tourIdx` (an order found by a heuristic search, not
proved optimal), and returns to `1`:

* `irrepProg_visits_all`: every one of the 194 rows is visited;
* `irrepProg_visits_degree`: at that moment the FRACTRAN state is the degree `irrepDegree k`;
* `irrepProg_closed`: the run ends back at the trivial representation;
* `irrepProg_length`: the program has 1316 instructions;
* `irrepTourEvidence`: the coverage statement as kernel-established SpectrumVM `Evidence`.
-/

namespace Dasein15VM.Irreps

open MonsterWalkZKP
open SpectrumVM (Evidence VerificationClaim)

variable {n : ℕ}

/-! ## Straight-line moves between shapes -/

theorem runOps_replicate_inc (i : Fin n) (k : ℕ) (v : PrimeShape n) :
    runOps (List.replicate k (.inc i)) v = some (Function.update v i (v i + k)) := by
  induction k generalizing v with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, runOps_cons]
    simp only [Op.exec, Option.bind_some, ih, Function.update_self, Function.update_idem]
    rw [show v i + 1 + k = v i + (k + 1) by omega]

theorem runOps_replicate_dec (i : Fin n) (k : ℕ) (v : PrimeShape n) (hk : k ≤ v i) :
    runOps (List.replicate k (.dec i)) v = some (Function.update v i (v i - k)) := by
  induction k generalizing v with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, runOps_cons]
    simp only [Op.exec, if_pos (show 0 < v i by omega), Option.bind_some]
    rw [ih _ (by simp; omega)]
    simp only [Function.update_self, Function.update_idem]
    rw [show v i - 1 - k = v i - (k + 1) by omega]

/-- The instructions for coordinate `i` of a move from `u` to `w`. -/
def stepsAt (i : Fin n) (u w : PrimeShape n) : List (Op n) :=
  List.replicate (u i - w i) (.dec i) ++ List.replicate (w i - u i) (.inc i)

theorem runOps_stepsAt (i : Fin n) (u w v : PrimeShape n) (hv : v i = u i) :
    runOps (stepsAt i u w) v = some (Function.update v i (w i)) := by
  rw [stepsAt, runOps_append, runOps_replicate_dec _ _ _ (by omega), Option.bind_some,
    runOps_replicate_inc]
  simp only [Function.update_self, Function.update_idem]
  congr 3; omega

theorem runOps_flatMap_stepsAt (u w : PrimeShape n) :
    ∀ (L : List (Fin n)), L.Nodup → ∀ v : PrimeShape n, (∀ j ∈ L, v j = u j) →
      runOps (L.flatMap fun i => stepsAt i u w) v = some (fun j => if j ∈ L then w j else v j)
  | [], _, v, _ => by simp
  | i :: L, hL, v, hv => by
    rw [List.nodup_cons] at hL
    rw [List.flatMap_cons, runOps_append, runOps_stepsAt _ _ _ _ (hv i (by simp)),
      Option.bind_some, runOps_flatMap_stepsAt u w L hL.2]
    · congr 1; funext j
      by_cases hj : j = i
      · subst hj; simp [hL.1]
      · simp [hj]
    · intro j hj
      have : j ≠ i := fun e => hL.1 (e ▸ hj)
      rw [Function.update_of_ne this]; exact hv j (by simp [hj])

/-- The straight-line program from `u` to `w`. -/
def moveProg (u w : PrimeShape n) : List (Op n) := (List.finRange n).flatMap fun i => stepsAt i u w

/-- **The move program takes `u` to `w` without faulting.** -/
theorem runOps_moveProg (u w : PrimeShape n) : runOps (moveProg u w) u = some w := by
  rw [moveProg, runOps_flatMap_stepsAt u w _ (List.nodup_finRange n) u (fun _ _ => rfl)]
  simp

/-! ## Tours -/

/-- The program visiting the shapes `ts` in order, starting from `v₀`. -/
def tourProg : PrimeShape n → List (PrimeShape n) → List (Op n)
  | _, [] => []
  | u, w :: ws => moveProg u w ++ tourProg w ws

/-- The run of `prog` from `v₀` passes through `t`: some prefix of the program ends at `t`. -/
def Visits (prog : List (Op n)) (v₀ t : PrimeShape n) : Prop :=
  ∃ m, runOps (prog.take m) v₀ = some t

/-- **A tour visits every one of its targets.** -/
theorem tourProg_visits (v₀ : PrimeShape n) (ts : List (PrimeShape n)) (t : PrimeShape n)
    (ht : t ∈ ts) : Visits (tourProg v₀ ts) v₀ t := by
  induction ts generalizing v₀ with
  | nil => simp at ht
  | cons w ws ih =>
    rcases List.mem_cons.1 ht with rfl | ht
    · refine ⟨(moveProg v₀ t).length, ?_⟩
      rw [tourProg, List.take_left' rfl, runOps_moveProg]
    · obtain ⟨m, hm⟩ := ih w ht
      refine ⟨(moveProg v₀ w).length + m, ?_⟩
      rw [tourProg, List.take_length_add_append, runOps_append, runOps_moveProg, Option.bind_some,
        hm]

/-- A tour ends at its last target. -/
theorem runOps_tourProg (v₀ : PrimeShape n) (ts : List (PrimeShape n)) :
    runOps (tourProg v₀ ts) v₀ = some (ts.getLast?.getD v₀) := by
  induction ts generalizing v₀ with
  | nil => rfl
  | cons w ws ih =>
    rw [tourProg, runOps_append, runOps_moveProg, Option.bind_some, ih]
    cases ws with
    | nil => simp
    | cons h t => rw [List.getLast?_eq_some_getLast (by simp)]; rfl

/-- Along a visit, the FRACTRAN state is the Gödel number of the visited shape. -/
theorem Visits.godel {prog : List (Op n)} {v₀ t : PrimeShape n} (B : PrimeBasis n)
    (h : Visits prog v₀ t) : ∃ m, (runOps (prog.take m) v₀).map (Dasein15VM.godel B) =
      some (Dasein15VM.godel B t) := by
  obtain ⟨m, hm⟩ := h
  exact ⟨m, by rw [hm]; rfl⟩

/-! ## Why both `inc` and `dec` are needed -/

/-- An increment-only program never lowers an exponent. -/
theorem runOps_inc_mono :
    ∀ (p : List (Op n)), (∀ o ∈ p, ∃ i, o = .inc i) → ∀ v w : PrimeShape n,
      runOps p v = some w → ∀ j, v j ≤ w j
  | [], _, v, w, h, j => by simp at h; subst h; exact le_rfl
  | o :: p, hp, v, w, h, j => by
    obtain ⟨i, rfl⟩ := hp o (by simp)
    rw [runOps_cons] at h
    simp only [Op.exec, Option.bind_some] at h
    have := runOps_inc_mono p (fun o ho => hp o (by simp [ho])) _ w h j
    refine le_trans ?_ this
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]

/-- The shapes visited by an increment-only program form a chain. -/
theorem inc_only_visits_chain (p : List (Op n)) (hp : ∀ o ∈ p, ∃ i, o = .inc i)
    {v₀ a b : PrimeShape n} (ha : Visits p v₀ a) (hb : Visits p v₀ b) :
    (∀ j, a j ≤ b j) ∨ (∀ j, b j ≤ a j) := by
  have key : ∀ {a b : PrimeShape n} {m₁ m₂ : ℕ}, m₁ ≤ m₂ → runOps (p.take m₁) v₀ = some a →
      runOps (p.take m₂) v₀ = some b → ∀ j, a j ≤ b j := by
    intro a b m₁ m₂ hm h₁ h₂
    have e : p.take m₂ = p.take m₁ ++ (p.take m₂).drop m₁ := by
      conv_lhs => rw [← List.take_append_drop m₁ (p.take m₂)]
      rw [List.take_take, Nat.min_eq_left hm]
    rw [e, runOps_append, h₁, Option.bind_some] at h₂
    exact runOps_inc_mono _ (fun o ho => hp o
      ((List.drop_subset _ _).trans (List.take_subset _ _) ho)) a b h₂
  obtain ⟨m₁, h₁⟩ := ha
  obtain ⟨m₂, h₂⟩ := hb
  rcases le_total m₁ m₂ with hm | hm
  · exact Or.inl (key hm h₁ h₂)
  · exact Or.inr (key hm h₂ h₁)

/-- Rows 1 and 2 are incomparable. -/
theorem irrepExp_one_two_incomparable :
    ¬ (∀ j, irrepExp 1 j ≤ irrepExp 2 j) ∧ ¬ (∀ j, irrepExp 2 j ≤ irrepExp 1 j) := by
  decide +kernel

/-- **No increment-only program visits all irreducible representations**, from any start. -/
theorem no_inc_only_tour (p : List MonsterOp) (hp : ∀ o ∈ p, ∃ i, o = .inc i)
    (v₀ : PrimeShape 15) : ¬ ∀ k, Visits p v₀ (irrepExp k) := fun h =>
  (inc_only_visits_chain p hp (h 1) (h 2)).elim irrepExp_one_two_incomparable.1
    irrepExp_one_two_incomparable.2

/-! ## Why the mass-conserving VM cannot do it -/

/-- At most 17 rows share any given mass (17 rows have mass 26). -/
theorem irrep_level_count (m : ℕ) :
    ((List.finRange 194).filter fun k => mass (irrepExp k) = m).length ≤ 17 := by
  by_cases hm : m ≤ 56
  · have : ∀ m : Fin 57,
        ((List.finRange 194).filter fun k => mass (irrepExp k) = m).length ≤ 17 := by
      decide +kernel
    exact this ⟨m, by omega⟩
  · rw [List.filter_eq_nil_iff.2]
    · simp
    · intro k _
      have := irrep_mass_le k
      simp only [decide_eq_true_eq]; omega

theorem irrep_level_count_26 :
    ((List.finRange 194).filter fun k => mass (irrepExp k) = 26).length = 17 := by
  decide +kernel

open Classical in
/-- **A certified Dasein15-VM trace meets at most 17 of the 194 irreducible representations**
(and only ones whose mass is the VM's conserved mass). -/
theorem vm_trace_irreps_le (S : VMSpec 15) {s₀ s : VMState 15} {tr : List (VMState 15)}
    (h : VMCorrect S s₀ s tr) :
    ((List.finRange 194).filter fun k => ∃ x ∈ tr, x.shape = irrepExp k).length ≤ 17 := by
  refine le_trans (List.Sublist.length_le ?_) (irrep_level_count S.mass)
  apply List.monotone_filter_right
  intro k hk
  simp only [decide_eq_true_eq] at hk ⊢
  obtain ⟨x, hx, e⟩ := hk
  rw [← e]
  exact (h.2.2.2 x hx).2.2

/-- In particular no certified VM trace visits all 194 irreducible representations. -/
theorem vm_trace_not_all_irreps (S : VMSpec 15) {s₀ s : VMState 15} {tr : List (VMState 15)}
    (h : VMCorrect S s₀ s tr) : ¬ ∀ k : Fin 194, ∃ x ∈ tr, x.shape = irrepExp k := by
  intro hall
  have := vm_trace_irreps_le S h
  rw [List.filter_eq_self.2 (by intro k _; simpa using hall k)] at this
  simp at this

/-- **The Dasein15 walk meets no irreducible representation**: it runs at mass 63, and every row
has mass at most 56. -/
theorem dasein_trace_no_irrep : ∀ x ∈ daseinTrace, ∀ k, x.shape ≠ irrepExp k := by
  intro x hx k e
  have hc := checkVMTrace_sound daseinSpec s₀ sFinal daseinTrace checkVMTrace_dasein
  have h1 : mass x.shape = 63 := (hc.2.2.2 x hx).2.2
  have h2 := irrep_mass_le k
  rw [e] at h1; omega

/-! ## The irreducible-representation tour -/

/-- The visiting order: one representative row for each of the 170 distinct exponent vectors. -/
def tourIdx : List ℕ := [0, 1, 5, 12, 21, 31, 46, 108, 93, 116, 50, 23, 114, 51, 79, 37, 22, 9, 18, 19, 86, 30, 62, 166, 183, 143, 138, 164, 109, 8, 61, 117, 148, 178, 72, 64, 87, 38, 131, 146, 68, 75, 94, 187, 97, 60, 153, 95, 172, 120, 14, 141, 63, 145, 49, 45, 157, 136, 156, 40, 134, 111, 118, 96, 58, 42, 158, 147, 139, 171, 122, 101, 192, 180, 174, 132, 80, 144, 125, 168, 115, 56, 112, 170, 67, 193, 188, 70, 160, 177, 76, 142, 185, 152, 100, 151, 159, 106, 25, 163, 104, 186, 167, 173, 98, 43, 65, 77, 130, 140, 175, 162, 121, 181, 91, 27, 119, 154, 150, 191, 90, 36, 66, 92, 88, 189, 184, 176, 73, 57, 35, 20, 69, 78, 103, 29, 113, 165, 52, 190, 149, 155, 110, 182, 127, 82, 126, 137, 54, 15, 84, 133, 48, 169, 161, 129, 28, 33, 17, 3, 11, 7, 6, 10, 32, 34, 24, 13, 4, 2]

/-- The visited rows, in order. -/
def tourRows : List (List ℕ) := [
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1],
  [0, 0, 0, 0, 0, 2, 0, 0, 1, 1, 0, 1, 0, 1, 1],
  [0, 0, 0, 4, 1, 2, 0, 0, 0, 1, 0, 1, 1, 1, 1],
  [0, 0, 0, 5, 0, 2, 0, 1, 1, 1, 0, 1, 1, 1, 1],
  [0, 0, 1, 5, 0, 3, 0, 0, 1, 1, 1, 1, 1, 1, 1],
  [1, 0, 0, 5, 2, 3, 0, 1, 1, 1, 1, 0, 1, 1, 1],
  [3, 0, 0, 6, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [3, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 1, 0, 1, 1],
  [2, 1, 2, 6, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [2, 2, 0, 6, 2, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1],
  [3, 2, 0, 4, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1],
  [3, 2, 0, 4, 2, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [2, 2, 0, 5, 2, 2, 0, 1, 1, 0, 1, 1, 1, 1, 1],
  [2, 1, 2, 5, 2, 3, 0, 1, 1, 0, 1, 1, 1, 1, 1],
  [1, 0, 2, 4, 1, 3, 0, 1, 1, 1, 1, 1, 1, 0, 1],
  [1, 0, 2, 1, 1, 3, 1, 1, 0, 1, 1, 1, 1, 0, 1],
  [0, 0, 2, 4, 0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 1],
  [0, 0, 2, 5, 1, 2, 1, 0, 1, 0, 1, 0, 0, 1, 1],
  [1, 1, 2, 5, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1],
  [0, 0, 5, 6, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [0, 1, 7, 5, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1],
  [3, 0, 7, 5, 0, 2, 0, 0, 1, 1, 1, 0, 1, 1, 1],
  [3, 1, 7, 5, 2, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1],
  [2, 0, 7, 5, 2, 3, 1, 0, 0, 1, 1, 1, 1, 1, 1],
  [2, 0, 7, 4, 2, 3, 0, 1, 0, 1, 1, 1, 1, 1, 1],
  [1, 0, 5, 4, 2, 3, 0, 1, 1, 1, 1, 1, 1, 1, 1],
  [1, 2, 3, 4, 2, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [0, 6, 3, 2, 2, 3, 1, 1, 1, 1, 1, 1, 0, 1, 1],
  [0, 6, 0, 1, 0, 2, 1, 1, 0, 0, 1, 0, 0, 1, 1],
  [0, 6, 0, 5, 0, 2, 0, 1, 1, 1, 1, 1, 1, 1, 1],
  [3, 6, 0, 6, 1, 2, 1, 0, 1, 1, 1, 1, 1, 1, 1],
  [2, 4, 1, 6, 2, 3, 1, 1, 1, 1, 1, 1, 1, 1, 0],
  [0, 4, 0, 6, 2, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [0, 3, 1, 6, 0, 3, 1, 1, 1, 1, 0, 1, 1, 1, 1],
  [6, 3, 0, 6, 1, 3, 1, 1, 0, 0, 0, 1, 1, 1, 1],
  [3, 2, 0, 6, 2, 3, 1, 0, 1, 0, 1, 1, 1, 1, 1],
  [2, 0, 0, 6, 2, 3, 1, 0, 1, 0, 1, 1, 1, 1, 0],
  [2, 0, 2, 6, 2, 3, 1, 0, 1, 1, 1, 1, 1, 1, 1],
  [2, 0, 1, 6, 2, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [3, 0, 2, 3, 2, 3, 1, 1, 1, 1, 0, 1, 1, 1, 1],
  [3, 0, 3, 5, 0, 3, 1, 1, 0, 1, 1, 1, 1, 1, 1],
  [6, 1, 2, 5, 1, 2, 1, 1, 0, 1, 1, 1, 1, 1, 1],
  [7, 2, 1, 4, 2, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [11, 2, 0, 3, 1, 3, 1, 0, 1, 1, 1, 1, 1, 1, 1],
  [12, 1, 0, 1, 2, 2, 0, 1, 1, 1, 1, 1, 1, 1, 1],
  [10, 1, 0, 5, 2, 3, 0, 1, 1, 1, 1, 1, 1, 1, 1],
  [10, 1, 2, 5, 0, 3, 0, 1, 0, 1, 1, 1, 1, 1, 1],
  [12, 6, 2, 5, 0, 3, 1, 1, 1, 0, 1, 0, 1, 1, 1],
  [13, 0, 2, 5, 2, 3, 0, 0, 1, 1, 0, 1, 1, 1, 1],
  [12, 0, 0, 4, 1, 2, 0, 0, 0, 0, 1, 0, 0, 1, 1],
  [16, 1, 0, 4, 2, 2, 1, 1, 0, 1, 1, 1, 1, 1, 1],
  [16, 3, 2, 0, 1, 2, 1, 0, 0, 1, 1, 1, 1, 1, 1],
  [18, 3, 2, 1, 2, 3, 0, 1, 1, 1, 0, 1, 1, 1, 1],
  [19, 1, 1, 1, 2, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1],
  [18, 1, 2, 5, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1],
  [20, 0, 2, 5, 0, 3, 1, 0, 1, 1, 1, 1, 0, 1, 1],
  [21, 0, 0, 6, 1, 3, 1, 1, 0, 1, 0, 1, 0, 1, 1],
  [18, 0, 0, 6, 1, 3, 1, 1, 0, 1, 0, 1, 1, 1, 1],
  [18, 0, 0, 6, 1, 3, 1, 1, 0, 1, 0, 1, 0, 0, 0],
  [18, 0, 0, 6, 1, 3, 1, 1, 1, 1, 1, 1, 1, 0, 0],
  [18, 0, 0, 6, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [18, 0, 8, 5, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1],
  [18, 3, 8, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1],
  [17, 0, 5, 0, 2, 3, 1, 1, 0, 0, 1, 0, 0, 1, 1],
  [18, 0, 0, 0, 1, 3, 1, 1, 1, 0, 0, 1, 1, 1, 1],
  [32, 0, 1, 0, 0, 3, 1, 1, 1, 1, 1, 0, 1, 1, 1],
  [32, 0, 9, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, 1],
  [42, 0, 7, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1],
  [42, 0, 0, 0, 0, 2, 0, 0, 1, 1, 1, 1, 1, 1, 1],
  [43, 0, 0, 0, 2, 2, 0, 1, 1, 1, 0, 1, 0, 1, 0],
  [46, 0, 0, 0, 2, 3, 0, 0, 1, 0, 1, 0, 1, 0, 0],
  [46, 2, 0, 0, 2, 0, 1, 0, 1, 0, 0, 1, 1, 1, 1],
  [44, 0, 0, 6, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1],
  [42, 2, 1, 4, 0, 2, 0, 0, 1, 1, 0, 1, 0, 1, 0],
  [42, 0, 0, 4, 1, 0, 0, 0, 1, 0, 1, 1, 1, 1, 0],
  [31, 1, 0, 3, 2, 0, 1, 1, 0, 1, 1, 1, 1, 0, 0],
  [28, 1, 0, 1, 1, 2, 1, 0, 1, 1, 1, 1, 1, 1, 1],
  [20, 2, 0, 0, 2, 3, 1, 0, 1, 1, 1, 1, 1, 1, 1],
  [18, 19, 0, 0, 0, 3, 0, 0, 0, 1, 1, 1, 0, 1, 1],
  [7, 9, 0, 0, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [5, 7, 1, 1, 1, 3, 1, 1, 0, 1, 1, 1, 1, 0, 1],
  [4, 12, 0, 1, 2, 3, 0, 1, 0, 1, 1, 1, 1, 1, 1],
  [0, 12, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [1, 12, 2, 1, 0, 3, 1, 0, 1, 1, 1, 1, 0, 1, 1],
  [0, 12, 7, 0, 0, 3, 1, 0, 1, 1, 1, 1, 1, 1, 1],
  [0, 17, 7, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1],
  [0, 18, 9, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1],
  [0, 17, 7, 4, 2, 2, 0, 0, 0, 0, 1, 0, 0, 1, 1],
  [0, 17, 7, 0, 1, 2, 0, 0, 0, 1, 1, 1, 1, 1, 1],
  [0, 17, 2, 0, 0, 2, 0, 0, 1, 1, 1, 1, 1, 1, 1],
  [0, 17, 1, 0, 2, 2, 1, 1, 1, 0, 1, 1, 1, 1, 1],
  [0, 18, 0, 1, 2, 2, 0, 1, 1, 1, 1, 1, 1, 1, 1],
  [0, 19, 0, 0, 2, 3, 0, 1, 0, 1, 1, 1, 1, 1, 1],
  [0, 19, 0, 0, 2, 3, 0, 1, 0, 1, 1, 1, 1, 1, 0],
  [1, 19, 1, 1, 2, 3, 0, 1, 0, 1, 1, 1, 1, 1, 0],
  [0, 19, 0, 1, 2, 3, 1, 1, 1, 1, 0, 1, 1, 0, 1],
  [0, 19, 0, 0, 2, 3, 1, 0, 1, 1, 0, 0, 1, 1, 1],
  [0, 19, 0, 0, 2, 3, 1, 0, 1, 1, 0, 0, 0, 0, 0],
  [2, 19, 0, 0, 2, 3, 1, 0, 1, 1, 1, 1, 0, 1, 1],
  [1, 19, 0, 4, 2, 3, 1, 0, 1, 1, 0, 1, 0, 0, 0],
  [2, 19, 0, 4, 0, 3, 0, 0, 0, 1, 1, 1, 1, 1, 1],
  [0, 18, 0, 5, 0, 2, 1, 1, 0, 0, 1, 1, 1, 1, 1],
  [0, 12, 0, 6, 0, 3, 1, 1, 1, 1, 1, 1, 1, 0, 1],
  [0, 13, 0, 6, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1],
  [1, 12, 0, 6, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0],
  [3, 17, 0, 1, 1, 2, 1, 0, 1, 1, 1, 0, 0, 1, 1],
  [6, 17, 0, 4, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 1],
  [1, 17, 2, 5, 0, 0, 0, 1, 1, 1, 1, 0, 1, 1, 1],
  [1, 17, 1, 5, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1],
  [0, 20, 0, 6, 2, 0, 1, 0, 0, 1, 1, 1, 0, 1, 1],
  [1, 19, 0, 4, 2, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1],
  [0, 19, 5, 1, 2, 0, 0, 1, 1, 1, 0, 1, 1, 0, 1],
  [0, 12, 5, 3, 2, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1],
  [0, 9, 7, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1],
  [0, 6, 7, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 1, 1],
  [3, 6, 8, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1],
  [4, 7, 7, 1, 1, 3, 0, 1, 1, 0, 1, 1, 1, 1, 1],
  [3, 6, 7, 5, 1, 2, 0, 1, 0, 1, 1, 1, 0, 1, 1],
  [1, 6, 8, 6, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1],
  [1, 3, 8, 4, 0, 3, 0, 0, 1, 1, 1, 1, 1, 1, 0],
  [1, 3, 8, 4, 1, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1],
  [2, 3, 7, 4, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1],
  [1, 1, 8, 4, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [1, 0, 8, 6, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1],
  [1, 0, 8, 6, 1, 3, 1, 0, 1, 1, 0, 1, 1, 1, 1],
  [0, 0, 9, 6, 2, 2, 1, 1, 1, 1, 0, 1, 0, 1, 1],
  [0, 0, 9, 3, 2, 3, 1, 1, 1, 1, 1, 1, 1, 1, 0],
  [0, 0, 9, 1, 2, 3, 1, 1, 1, 1, 1, 1, 0, 0, 1],
  [0, 0, 7, 1, 1, 2, 1, 1, 0, 1, 1, 1, 1, 1, 1],
  [3, 0, 8, 1, 0, 3, 1, 1, 0, 1, 0, 1, 0, 1, 1],
  [2, 0, 7, 0, 0, 2, 0, 1, 0, 0, 1, 1, 1, 1, 1],
  [2, 0, 9, 0, 1, 2, 1, 0, 1, 1, 1, 1, 1, 1, 1],
  [4, 3, 7, 0, 2, 2, 0, 0, 1, 1, 1, 1, 1, 1, 1],
  [0, 3, 7, 1, 2, 3, 0, 0, 1, 1, 1, 1, 1, 1, 1],
  [0, 3, 7, 0, 1, 2, 1, 0, 1, 1, 0, 0, 1, 1, 1],
  [0, 3, 9, 0, 1, 3, 1, 1, 1, 1, 0, 1, 1, 1, 1],
  [0, 1, 9, 0, 2, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [0, 1, 9, 0, 2, 3, 0, 1, 1, 1, 1, 1, 0, 1, 0],
  [1, 2, 9, 1, 2, 3, 0, 1, 1, 1, 1, 1, 1, 1, 1],
  [2, 2, 9, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [2, 2, 9, 4, 2, 3, 0, 1, 1, 1, 1, 1, 0, 0, 1],
  [2, 0, 9, 4, 1, 3, 0, 1, 1, 0, 0, 1, 1, 1, 1],
  [2, 0, 9, 6, 0, 3, 1, 1, 0, 0, 1, 1, 1, 1, 1],
  [1, 0, 9, 6, 2, 2, 1, 1, 0, 1, 1, 0, 1, 1, 0],
  [1, 1, 9, 6, 2, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1],
  [0, 2, 9, 6, 2, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1],
  [0, 2, 9, 6, 1, 2, 1, 1, 0, 0, 0, 1, 1, 1, 1],
  [0, 0, 9, 6, 2, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1],
  [0, 0, 9, 6, 2, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0],
  [2, 0, 9, 6, 2, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1],
  [3, 0, 8, 6, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1],
  [5, 0, 8, 4, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0],
  [6, 0, 9, 4, 2, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1],
  [12, 1, 9, 1, 0, 2, 1, 1, 0, 1, 1, 1, 1, 1, 1],
  [9, 1, 8, 1, 1, 3, 0, 1, 1, 1, 1, 0, 1, 1, 1],
  [7, 0, 2, 0, 1, 3, 0, 1, 1, 0, 1, 1, 1, 1, 1],
  [4, 0, 2, 0, 0, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [3, 0, 0, 1, 0, 3, 1, 0, 0, 1, 1, 1, 1, 1, 1],
  [1, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1, 0, 1, 1, 0],
  [0, 1, 0, 0, 1, 2, 1, 0, 1, 1, 1, 1, 1, 1, 0],
  [1, 1, 0, 1, 1, 2, 0, 1, 1, 0, 0, 1, 1, 1, 0],
  [1, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 1, 1],
  [0, 3, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1],
  [0, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [0, 2, 1, 0, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [0, 0, 3, 1, 2, 2, 0, 0, 1, 1, 1, 1, 1, 1, 1],
  [1, 0, 2, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1],
  [2, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1],
  [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1]]

theorem tourRows_eq : tourIdx.map irrepRow = tourRows := by decide +kernel

/-- Every row of the table occurs among the visited rows. -/
theorem tourRows_covers : ∀ r ∈ irrepExpList, r ∈ tourRows := by decide +kernel

/-- The tour targets: the 170 visited shapes, then back to the trivial representation. -/
def irrepTour : List (PrimeShape 15) := tourRows.map toShape ++ [irrepExp 0]

/-- **The irreducible-representation tour**, as a Monster VM program. -/
def irrepProg : List MonsterOp := tourProg (irrepExp 0) irrepTour

theorem irrepExp_mem_irrepTour (k : Fin 194) : irrepExp k ∈ irrepTour := by
  have hk : irrepRow k ∈ irrepExpList := by
    rw [irrepRow, List.getD_eq_getElem _ _ (by rw [show irrepExpList.length = 194 from rfl]; exact k.2)]
    exact List.getElem_mem _
  exact List.mem_append_left _ (List.mem_map_of_mem (tourRows_covers _ hk))

/-- **Every irreducible representation of the Monster is visited.** -/
theorem irrepProg_visits_all (k : Fin 194) : Visits irrepProg (irrepExp 0) (irrepExp k) :=
  tourProg_visits _ _ _ (irrepExp_mem_irrepTour k)

/-- When row `k` is visited, the FRACTRAN state is the degree `irrepDegree k`: the run, started at
`1`, passes through every irreducible degree. -/
theorem irrepProg_visits_degree (k : Fin 194) :
    ∃ m, (runOps (irrepProg.take m) (irrepExp 0)).map (godel sspBasis) = some (irrepDegree k) :=
  (irrepProg_visits_all k).godel sspBasis

/-- The tour is closed: it ends at the trivial representation. -/
theorem irrepProg_closed : runOps irrepProg (irrepExp 0) = some (irrepExp 0) := by
  rw [irrepProg, runOps_tourProg, irrepTour, List.getLast?_append]
  simp

/-- The tour has 1316 instructions. -/
theorem irrepProg_length : irrepProg.length = 1316 := by decide +kernel

/-- Kernel-established SpectrumVM evidence for the coverage statement. -/
def irrepTourEvidence (claim : VerificationClaim) :
    Evidence (∀ k : Fin 194, Visits irrepProg (irrepExp 0) (irrepExp k)) :=
  .kernel irrepProg_visits_all claim

theorem irrepTourEvidence_assurance (claim : VerificationClaim) :
    (irrepTourEvidence claim).assurance = .kernelEstablished := rfl

end Dasein15VM.Irreps
