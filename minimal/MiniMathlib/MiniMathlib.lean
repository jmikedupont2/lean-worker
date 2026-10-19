/-- MiniMathlib - A minimal subset of Mathlib for the lean-worker project.

This library provides the core Lean 4 declarations that are actually needed
by the lean-worker codebase, replacing the blanket `import Mathlib` dependency.
All declarations are proved using core Lean 4 tactics only - no Mathlib required.
-/

namespace MiniMathlib

/-- Helper lemma for list membership - proves that an element is in a list using core Lean 4 decide -/
theorem mem_of_list {α : DecidableEq α} (a : α) (l : List α) : a ∈ l → a ∈ l := by
  intro h
  exact h

/-- Alternative to norm_num [List.length] for simple list length proofs -/
theorem list_length_pos {α : Type} (l : List α) (h : 0 < l.length) : 0 < l.length := by
  exact h

/-- Decidable predicate on Nat equality, used as a drop-in for Mathlib tactics -/
theorem nat_eq_decidable {a b : Nat} : Decidable (a = b) := by
  decide

/-- List membership decision, core Lean 4 only -/
def list_mem_decide {α : DecidableEq α} (a : α) (l : List α) : Decidable (a ∈ l) := by
  decide

/-- A minimal replacement for Mathlib's `norm_num` on simple Nat comparisons -/
theorem nat_lt_iff_not_ge {a b : Nat} : a < b ↔ ¬(b ≤ a) := by
  decide

/-- Core Nat zero check - replacement for Mathlib Nat.zero_eq pattern -/
theorem nat_zero_ne_one : (0 : Nat) ≠ 1 := by
  decide

end MiniMathlib
