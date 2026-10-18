module

/-!
# Reflective edge-direction check

A *declaration graph* is plain data: declarations are numbered `0, 1, …`, each one is assigned
to a chunk (also a number), and each edge `(i, j)` says that declaration `i` uses
declaration `j` (in its statement or its proof). `mayDependOn` lists the ordered chunk pairs
`(a, b)` for which chunk `a` is allowed to use chunk `b`; a chunk may always use itself.

`DeclGraph.valid` is a Boolean checker, and `DeclGraph.valid_iff` proves that it returns `true`
exactly when the graph has no back-edge (`DeclGraph.NoBackEdge`). So a closed proof of
`g.valid = true` by kernel evaluation (`decide +kernel`) is a proof of `g.NoBackEdge`.

When the allowed pairs only point to a strictly smaller chunk number (`DeclGraph.Layered`),
`chunk_le_of_reach` shows that every dependency path, of any length, runs from a chunk to the
same or a lower chunk, and `chunk_eq_of_cycle` shows that no dependency cycle crosses chunks.

These statements are about the data. The step from a Lean environment to the data is done by
the (unverified) metaprogram in `RequestProject/ReflectGraph.lean`.
-/

public section

namespace Decouple.Reflect

/-- A reified declaration graph: chunk of each declaration, use-edges, allowed chunk pairs. -/
structure DeclGraph where
  /-- `chunkOf[i]` is the chunk of declaration `i`. -/
  chunkOf : List Nat
  /-- `(i, j)`: declaration `i` uses declaration `j`. -/
  edges : List (Nat × Nat)
  /-- `(a, b)`: chunk `a` may use chunk `b` (in addition to itself). -/
  mayDependOn : List (Nat × Nat)

namespace DeclGraph

/-- The chunk of declaration `i`, if `i` is a declaration of the graph. -/
def chunk? (g : DeclGraph) (i : Nat) : Option Nat := g.chunkOf[i]?

/-- May chunk `a` use chunk `b`? -/
def allowed (g : DeclGraph) (a b : Nat) : Bool :=
  a == b || g.mayDependOn.contains (a, b)

/-- Is this edge between two known declarations, in an allowed direction? -/
def edgeOk (g : DeclGraph) (e : Nat × Nat) : Bool :=
  match g.chunk? e.1, g.chunk? e.2 with
  | some a, some b => g.allowed a b
  | _, _ => false

/-- The Boolean checker. -/
def valid (g : DeclGraph) : Bool := g.edges.all g.edgeOk

/-- Specification: every edge joins two declarations of the graph, and goes from a chunk to
itself or to a chunk it may depend on. -/
def NoBackEdge (g : DeclGraph) : Prop :=
  ∀ e ∈ g.edges, ∃ a b, g.chunk? e.1 = some a ∧ g.chunk? e.2 = some b ∧
    (a = b ∨ (a, b) ∈ g.mayDependOn)

theorem edgeOk_iff (g : DeclGraph) (e : Nat × Nat) :
    g.edgeOk e = true ↔ ∃ a b, g.chunk? e.1 = some a ∧ g.chunk? e.2 = some b ∧
      (a = b ∨ (a, b) ∈ g.mayDependOn) := by
  unfold edgeOk allowed
  cases g.chunk? e.1 <;> cases g.chunk? e.2 <;> simp

/-- Soundness and completeness of the checker. -/
theorem valid_iff (g : DeclGraph) : g.valid = true ↔ g.NoBackEdge := by
  simp only [valid, List.all_eq_true, NoBackEdge, edgeOk_iff]

/-- Soundness, in the form used after `decide +kernel`. -/
theorem noBackEdge_of_valid {g : DeclGraph} (h : g.valid = true) : g.NoBackEdge :=
  (valid_iff g).1 h

/-- A checker failure is a real back-edge (completeness, contrapositive form). -/
theorem exists_backEdge_of_valid_false {g : DeclGraph} (h : g.valid = false) :
    ∃ e ∈ g.edges, g.edgeOk e = false := by
  simpa [valid, List.all_eq_false] using h

/-- Dependency paths (reflexive–transitive closure of the use-edges). -/
inductive Reach (g : DeclGraph) : Nat → Nat → Prop
  | refl (i : Nat) : Reach g i i
  | step {i j k : Nat} : (i, j) ∈ g.edges → Reach g j k → Reach g i k

/-- The allowed chunk pairs follow a numbering of the chunks: a chunk may only use chunks with
a smaller number. -/
def Layered (g : DeclGraph) : Prop := ∀ p ∈ g.mayDependOn, p.2 < p.1

/-- Along any dependency path the chunk number never increases. -/
theorem chunk_le_of_reach {g : DeclGraph} (hg : g.NoBackEdge) (hl : g.Layered)
    {i j : Nat} (hr : g.Reach i j) {a b : Nat} (ha : g.chunk? i = some a)
    (hb : g.chunk? j = some b) : b ≤ a := by
  induction hr generalizing a with
  | refl i =>
    rw [ha] at hb
    cases hb
    exact Nat.le_refl _
  | step he _ ih =>
    obtain ⟨a', c, ha', hc, hac⟩ := hg _ he
    rw [ha] at ha'
    cases ha'
    have := ih hc hb
    rcases hac with rfl | hmem
    · exact this
    · exact Nat.le_trans this (Nat.le_of_lt (hl _ hmem))

/-- No dependency cycle crosses chunks: mutually dependent declarations share a chunk. -/
theorem chunk_eq_of_cycle {g : DeclGraph} (hg : g.NoBackEdge) (hl : g.Layered)
    {i j : Nat} (hij : g.Reach i j) (hji : g.Reach j i) {a b : Nat}
    (ha : g.chunk? i = some a) (hb : g.chunk? j = some b) : a = b :=
  Nat.le_antisymm (chunk_le_of_reach hg hl hji hb ha) (chunk_le_of_reach hg hl hij ha hb)

/-- The layering condition is decidable by evaluation too. -/
def layeredB (g : DeclGraph) : Bool := g.mayDependOn.all fun p => decide (p.2 < p.1)

theorem layered_of_layeredB {g : DeclGraph} (h : g.layeredB = true) : g.Layered := by
  simpa [layeredB, Layered] using h

end DeclGraph

end Decouple.Reflect

end
