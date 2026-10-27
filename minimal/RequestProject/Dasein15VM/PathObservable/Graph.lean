import RequestProject.Dasein15VM.PathObservable.Observables

/-!
# Path observables, part 3: the path graph and path classes

The certified local rewrite is **extension**: append the VM successor of the last state
(`Extend S a b`).  It is directed, deterministic, and preserves certification.

* `Certified S tr`: `tr` is a certified trace (`certified_iff`: some `VMCorrect S s₀ s tr`).
* `Reachable S := ReflTransGen (Extend S)` — the reachability relation of the path graph
  `PathGraph S`.
* `reachable_iff_prefix`: from a certified trace, the reachable traces are exactly its certified
  extensions (`a <+: b ∧ Certified S b`).
* `reachable_antisymm`: reachability is a partial order — the directed graph has no cycles, so
  each directed path class is a single trace.
* `extend_deterministic` / `extend_exists`: each certified trace has exactly one extension
  (when the conserved mass is positive).
* `PathEquiv S := EqvGen (Extend S)` (the undirected closure).  `pathEquiv_iff_head`: two
  certified traces are equivalent iff they start at the same state.  So the undirected path
  classes are in bijection with invariant start states (`certified_singleton_iff`).
* Observables: `Descends S obs` (invariance under extension).  `Descends.pathEquiv`: a descending
  observable is constant on path classes.  `head?` descends; `traceLength` and
  `totalVariation` do not — they grow by `1` and `2` along each extension
  (`traceLength_extend`, `totalVariation_extend`): they are gradings of the directed graph, not
  class invariants.
-/

namespace Dasein15VM.Path

open Dasein15VM

variable {n : ℕ} {S : VMSpec n}

/-- The step relation. -/
def StepRel (S : VMSpec n) (a b : VMState n) : Prop := step S a = some b

/-- A certified trace: nonempty, a chain of VM steps, and every state invariant. -/
def Certified (S : VMSpec n) (tr : List (VMState n)) : Prop :=
  tr ≠ [] ∧ List.IsChain (StepRel S) tr ∧ ∀ x ∈ tr, VMInvariant S x

theorem certified_iff {tr : List (VMState n)} :
    Certified S tr ↔ ∃ s₀ s, VMCorrect S s₀ s tr := by
  constructor
  · rintro ⟨hne, hc, hi⟩
    exact ⟨tr.head hne, tr.getLast hne, List.head?_eq_some_head hne,
      List.getLast?_eq_some_getLast hne, List.isChain_iff_getElem.1 hc, hi⟩
  · rintro ⟨s₀, s, h⟩
    exact ⟨List.ne_nil_of_length_pos h.length_pos, List.isChain_iff_getElem.2 h.2.2.1, h.2.2.2⟩

/-- A one-state trace is certified iff its state is invariant. -/
theorem certified_singleton_iff {x : VMState n} : Certified S [x] ↔ VMInvariant S x := by
  simp [Certified]

/-- The certified local rewrite: extend by the VM successor of the last state. -/
def Extend (S : VMSpec n) (a b : List (VMState n)) : Prop :=
  ∃ x t, a.getLast? = some x ∧ step S x = some t ∧ b = a ++ [t]

/-- Reachability in the path graph. -/
def Reachable (S : VMSpec n) : List (VMState n) → List (VMState n) → Prop :=
  Relation.ReflTransGen (Extend S)

/-- The path graph of a spec: certified traces, extension edges, reachability. -/
structure PathGraph (S : VMSpec n) where
  nodes : Set (List (VMState n))
  edges : List (VMState n) → List (VMState n) → Prop
  nodes_eq : nodes = {tr | Certified S tr}
  edges_eq : edges = Extend S

/-- The path graph of `S`. -/
def pathGraph (S : VMSpec n) : PathGraph S := ⟨_, _, rfl, rfl⟩

theorem Certified.extend {a b : List (VMState n)} (ha : Certified S a) (h : Extend S a b) :
    Certified S b := by
  obtain ⟨x, t, hx, ht, rfl⟩ := h
  refine ⟨by simp, ha.2.1.append (List.isChain_singleton t) ?_, ?_⟩
  · intro x' hx' y hy
    rw [hx] at hx'; cases hx'
    simp at hy; subst hy; exact ht
  · intro y hy
    rcases List.mem_append.1 hy with hy | hy
    · exact ha.2.2 y hy
    · simp at hy; subst hy; exact step_preserves_invariant S ht

theorem extend_prefix {a b : List (VMState n)} (h : Extend S a b) :
    a <+: b ∧ b.length = a.length + 1 := by
  obtain ⟨x, t, -, -, rfl⟩ := h
  exact ⟨List.prefix_append _ _, by simp⟩

theorem extend_deterministic {a b c : List (VMState n)} (hb : Extend S a b) (hc : Extend S a c) :
    b = c := by
  obtain ⟨x, t, hx, ht, rfl⟩ := hb
  obtain ⟨x', t', hx', ht', rfl⟩ := hc
  rw [hx] at hx'; cases hx'
  rw [ht] at ht'; cases ht'
  rfl

/-- Liveness: a certified trace of a spec of positive mass always has an extension. -/
theorem extend_exists {a : List (VMState n)} (ha : Certified S a) (hm : 0 < S.mass) :
    ∃ b, Extend S a b := by
  have hx := ha.2.2 _ (List.getLast_mem ha.1)
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 (step_isSome S hm hx)
  exact ⟨_, _, t, List.getLast?_eq_some_getLast ha.1, ht, rfl⟩

theorem Reachable.prefix {a b : List (VMState n)} (h : Reachable S a b) : a <+: b := by
  induction h with
  | refl => exact List.prefix_refl _
  | tail _ hbc ih => exact ih.trans (extend_prefix hbc).1

theorem Reachable.certified {a b : List (VMState n)} (h : Reachable S a b) (ha : Certified S a) :
    Certified S b := by
  induction h with
  | refl => exact ha
  | tail _ hbc ih => exact ih.extend hbc

theorem Certified.of_append {a l : List (VMState n)} (h : Certified S (a ++ l)) (ha : a ≠ []) :
    Certified S a :=
  ⟨ha, h.2.1.left_of_append, fun x hx => h.2.2 x (List.mem_append_left _ hx)⟩

/-- **Reachability is the certified-prefix order.** -/
theorem reachable_iff_prefix {a b : List (VMState n)} (ha : Certified S a) :
    Reachable S a b ↔ a <+: b ∧ Certified S b := by
  refine ⟨fun h => ⟨h.prefix, h.certified ha⟩, ?_⟩
  rintro ⟨⟨l, rfl⟩, hb⟩
  induction l using List.reverseRecOn with
  | nil => simpa using Relation.ReflTransGen.refl
  | append_singleton l t ih =>
    rw [← List.append_assoc] at hb ⊢
    have hal : a ++ l ≠ [] := by simp [ha.1]
    refine Relation.ReflTransGen.tail (ih (hb.of_append hal)) ?_
    refine ⟨(a ++ l).getLast hal, t, List.getLast?_eq_some_getLast hal, ?_, rfl⟩
    exact (List.isChain_append.1 hb.2.1).2.2 _ (List.getLast?_eq_some_getLast hal) t (by simp)

/-- Reachability is antisymmetric: the path graph is directed and acyclic. -/
theorem reachable_antisymm {a b : List (VMState n)} (hab : Reachable S a b)
    (hba : Reachable S b a) : a = b :=
  hab.prefix.eq_of_length (le_antisymm hab.prefix.length_le hba.prefix.length_le)

/-- Two certified traces with the same start: the shorter is a prefix of the longer. -/
theorem prefix_of_head {a b : List (VMState n)} (ha : Certified S a) (hb : Certified S b)
    (hh : a.head? = b.head?) (hl : a.length ≤ b.length) : a <+: b := by
  obtain ⟨s₀, s, h⟩ := certified_iff.1 ha
  obtain ⟨s₀', s', h'⟩ := certified_iff.1 hb
  have : s₀ = s₀' := Option.some.inj (h.1.symm.trans (hh.trans h'.1))
  subst this
  rw [List.prefix_iff_eq_take]
  exact List.ext_getElem (by simp; omega) fun i hi hi' => by
    rw [List.getElem_take]; exact h.getElem_eq h' i hi _

/-- The undirected path-class relation. -/
def PathEquiv (S : VMSpec n) : List (VMState n) → List (VMState n) → Prop :=
  Relation.EqvGen (Extend S)

theorem extend_head {a b : List (VMState n)} (h : Extend S a b) : a.head? = b.head? := by
  obtain ⟨x, t, hx, -, rfl⟩ := h
  have : a ≠ [] := by rintro rfl; simp at hx
  rw [List.head?_append_of_ne_nil _ this]

theorem Reachable.pathEquiv {a b : List (VMState n)} (h : Reachable S a b) : PathEquiv S a b := by
  induction h with
  | refl => exact Relation.EqvGen.refl _
  | tail _ hbc ih => exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ hbc)

/-- An observable descends to path classes if it is invariant under extension. -/
def Descends {α : Type} (S : VMSpec n) (obs : List (VMState n) → α) : Prop :=
  ∀ a b, Extend S a b → obs a = obs b

/-- A descending observable is constant on path classes. -/
theorem Descends.pathEquiv {α : Type} {obs : List (VMState n) → α} (h : Descends S obs)
    {a b : List (VMState n)} (hab : PathEquiv S a b) : obs a = obs b := by
  induction hab with
  | rel x y hxy => exact h x y hxy
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

/-- The start state descends. -/
theorem head_descends : Descends S List.head? := fun _ _ h => extend_head h

/-- **Path classes are start states**: two certified traces are path-equivalent iff they start
at the same state. -/
theorem pathEquiv_iff_head {a b : List (VMState n)} (ha : Certified S a) (hb : Certified S b) :
    PathEquiv S a b ↔ a.head? = b.head? := by
  refine ⟨head_descends.pathEquiv, fun hh => ?_⟩
  rcases le_total a.length b.length with hl | hl
  · exact ((reachable_iff_prefix ha).2 ⟨prefix_of_head ha hb hh hl, hb⟩).pathEquiv
  · exact Relation.EqvGen.symm _ _
      ((reachable_iff_prefix hb).2 ⟨prefix_of_head hb ha hh.symm hl, ha⟩).pathEquiv

/-- Every certified trace is path-equivalent to the one-state trace of its start. -/
theorem pathEquiv_head_singleton {a : List (VMState n)} (ha : Certified S a) :
    PathEquiv S a [a.head ha.1] := by
  have hx : Certified S [a.head ha.1] := certified_singleton_iff.2 (ha.2.2 _ (List.head_mem _))
  rw [pathEquiv_iff_head ha hx]
  simp [List.head?_eq_some_head ha.1]

/-- `traceLength` grows by one along each extension. -/
theorem traceLength_extend {a b : List (VMState n)} (h : Extend S a b) :
    traceLength b = traceLength a + 1 := (extend_prefix h).2

/-- `traceLength` is not a class invariant as soon as some extension exists. -/
theorem traceLength_not_descends {a b : List (VMState n)} (h : Extend S a b) :
    ¬ Descends S traceLength := fun hd => by
  have := hd a b h
  rw [traceLength_extend h] at this
  omega

/-- `totalVariation` grows by two along each extension of a certified trace. -/
theorem totalVariation_extend {a b : List (VMState n)} (ha : Certified S a) (h : Extend S a b) :
    totalVariation b = totalVariation a + 2 := by
  obtain ⟨_, _, ha'⟩ := certified_iff.1 ha
  obtain ⟨_, _, hb'⟩ := certified_iff.1 (ha.extend h)
  rw [VMCorrect.totalVariation ha', VMCorrect.totalVariation hb', (extend_prefix h).2]
  have := ha'.length_pos
  omega

end Dasein15VM.Path
