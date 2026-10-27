import RequestProject.Dasein15VM.Walk

/-!
# Dasein15 VM: the numeric invariant `⌊‖v‖⌋ mod 8` along the walk

**This is not a Bott class.** `normMod8 k = k % 8` is applied to the floor of the Euclidean norm
of the exponent vector. It is a number that happens to be 8-periodic in `k`; it is not an element
of `KO⁻ⁿ(pt)`, it is not attached to any Clifford module, and nothing in this file is about Bott
periodicity. `Dasein15.bottClass` is the same function under a misleading name
(`normMod8_eq_dasein_bottClass`). Real Clifford algebras `Cl(p,q)` and the facts about them that
are proved in this project are in `RequestProject.Dasein15VM.KTheory`.

(This file was previously `Dasein15VM/Bott.lean`; the theorems are unchanged, only renamed.)

* `walk_normFloors`: the norm floors of the walk are the list `walkNormFloors` (each entry is
  certified by `k² ≤ ‖v‖² < (k+1)²`, checked in the kernel).
* `walk_normMod8_phase_starts`: at the phase starts (steps 0, 255, 314, 421) the values are
  2, 7, 7, 1, and at the final step 499 the value is 1 — the numbers written in
  `Dasein15.bott_trajectory` and `final_bott`.
* `walk_normMod8_all_values_each_phase`: within each of the four phases all 8 residues occur;
  `normMod8_varies_along_walk`: in particular the value is not constant on any phase.
-/

namespace Dasein15VM

open Dasein15

variable {n : ℕ}

/-- Squared Euclidean norm of a shape. -/
def sumSq (v : PrimeShape n) : ℕ := (List.ofFn fun i => v i * v i).sum

/-- Floor of the Euclidean norm of a shape. -/
def normFloor (v : PrimeShape n) : ℕ := Nat.sqrt (sumSq v)

/-- The residue mod 8 of a natural number (a numeric proxy, **not** a Bott class). -/
def normMod8 (k : ℕ) : Fin 8 := ⟨k % 8, Nat.mod_lt _ (by omega)⟩

/-- `Dasein15.bottClass` is exactly `normMod8`: a residue mod 8, not a K-theory class. -/
theorem normMod8_eq_dasein_bottClass : normMod8 = Dasein15.bottClass := rfl

/-- The numeric invariant `⌊‖v‖⌋ mod 8` of a shape. -/
def normMod8Of (v : PrimeShape n) : Fin 8 := normMod8 (normFloor v)

/-- Norm floors of the 500 states of the walk (a certificate, re-checked below). -/
def walkNormFloors : List ℕ := [34, 34, 34, 35, 35, 35, 35, 36, 36, 36, 37, 37, 38, 39, 39, 40, 41, 41, 42, 43, 44, 45, 46, 47, 48, 49, 48, 47, 46, 45, 44, 43, 43, 42, 41, 40, 40, 39, 39, 38, 38, 37, 37, 37, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 37, 37, 37, 38, 38, 39, 39, 40, 40, 41, 42, 43, 43, 44, 45, 46, 47, 48, 49, 50, 51, 50, 49, 48, 47, 46, 45, 44, 44, 43, 42, 41, 41, 40, 40, 39, 39, 38, 38, 37, 37, 37, 37, 37, 36, 36, 36, 37, 37, 37, 37, 37, 38, 38, 39, 39, 40, 40, 41, 41, 42, 43, 44, 44, 45, 46, 47, 48, 49, 50, 51, 52, 51, 50, 49, 48, 47, 46, 45, 45, 44, 43, 42, 42, 41, 40, 40, 39, 39, 39, 38, 38, 38, 37, 37, 37, 37, 37, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 41, 42, 42, 43, 44, 45, 45, 46, 47, 48, 49, 50, 51, 52, 53, 52, 51, 50, 49, 48, 47, 46, 45, 45, 44, 43, 43, 42, 41, 41, 40, 40, 39, 39, 39, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 39, 39, 39, 40, 40, 41, 41, 42, 43, 43, 44, 45, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 53, 52, 51, 50, 49, 48, 47, 46, 46, 45, 44, 44, 43, 42, 42, 41, 41, 40, 40, 40, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 40, 40, 40, 41, 41, 42, 42, 43, 44, 44, 45, 46, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 54, 53, 52, 51, 50, 49, 48, 47, 47, 46, 45, 45, 44, 43, 43, 42, 42, 41, 41, 40, 40, 40, 40, 39, 39, 39, 39, 39, 39, 39, 40, 40, 40, 40, 41, 41, 42, 42, 43, 43, 44, 45, 45, 46, 47, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 55, 54, 53, 52, 51, 50, 49, 48, 48, 47, 46, 45, 45, 44, 44, 43, 43, 42, 42, 41, 41, 41, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 41, 41, 41, 42, 42, 43, 43, 44, 44, 45, 45, 46, 47, 48, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 56, 55, 54, 53, 52, 51, 50, 49, 49, 48, 47, 46, 46, 45, 45, 44, 43, 43, 43, 42, 42, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 42, 42, 43, 43, 43, 44, 45, 45, 46, 46, 47, 48, 49, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 57, 56, 55, 54, 53, 52, 51, 50, 50, 49, 48, 47, 47, 46, 45, 45, 44, 44, 43, 43, 43, 42, 42, 42, 42, 41, 41, 41, 41, 41, 41, 42, 42, 42, 42, 43, 43, 43, 44, 44, 45, 45, 46, 47, 47, 48, 49]

/-- Kernel-checkable certificate that `k = ⌊√s⌋`. -/
def sqrtCert (s k : ℕ) : Bool := decide (k * k ≤ s ∧ s < (k + 1) * (k + 1))

theorem sqrtCert_iff (s k : ℕ) : sqrtCert s k = true ↔ Nat.sqrt s = k := by
  simp [sqrtCert, eq_comm (a := Nat.sqrt s), Nat.eq_sqrt]

theorem map_eq_of_cert {α : Type} (f : α → ℕ) :
    ∀ (l : List α) (ks : List ℕ), l.length = ks.length →
      (l.zip ks).all (fun p => sqrtCert (f p.1) p.2) = true → l.map (fun a => Nat.sqrt (f a)) = ks
  | [], [], _, _ => rfl
  | a :: l, k :: ks, hl, h => by
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at h
    simp only [List.map_cons, (sqrtCert_iff _ _).1 h.1,
      map_eq_of_cert f l ks (by simpa using hl) h.2]
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

set_option maxRecDepth 100000 in
theorem walkNormFloors_cert :
    daseinTrace.length = walkNormFloors.length ∧
      (daseinTrace.zip walkNormFloors).all (fun p => sqrtCert (sumSq p.1.shape) p.2) = true := by
  decide +kernel

/-- The norm floors along the walk. -/
theorem walk_normFloors : daseinTrace.map (fun s => normFloor s.shape) = walkNormFloors :=
  map_eq_of_cert (fun s : VMState 15 => sumSq s.shape) _ _ walkNormFloors_cert.1
    walkNormFloors_cert.2

/-- The values of `⌊‖v‖⌋ mod 8` along the walk. -/
theorem walk_normMod8 :
    daseinTrace.map (fun s => normMod8Of s.shape) = walkNormFloors.map normMod8 := by
  rw [← walk_normFloors, List.map_map]; rfl

/-- Values of `⌊‖v‖⌋ mod 8` at the phase starts (steps 0, 255, 314, 421) and at the final step 499. -/
theorem walk_normMod8_phase_starts :
    [0, 255, 314, 421, 499].map (fun k => (daseinTrace.map (fun s => normMod8Of s.shape))[k]?) =
      [some 2, some 7, some 7, some 1, some 1] := by
  rw [walk_normMod8]; decide +kernel

/-- Phase intervals of the walk, `[start, stop)`. -/
def phaseIntervals : List (ℕ × ℕ) := [(0, 255), (255, 314), (314, 421), (421, 500)]

/-- **Within each of the four phases of the walk, every residue mod 8 occurs.** -/
theorem walk_normMod8_all_values_each_phase :
    ∀ I ∈ phaseIntervals, ∀ b : Fin 8,
      b ∈ ((daseinTrace.map (fun s => normMod8Of s.shape)).take I.2).drop I.1 := by
  rw [walk_normMod8]; decide +kernel

/-- **`⌊‖v‖⌋ mod 8` is not constant on any phase**: each phase contains two states where it differs. -/
theorem normMod8_varies_along_walk :
    ∀ I ∈ phaseIntervals, ∃ t₁ t₂, I.1 ≤ t₁ ∧ t₁ < I.2 ∧ I.1 ≤ t₂ ∧ t₂ < I.2 ∧
      (daseinTrace.map (fun s => normMod8Of s.shape))[t₁]? ≠
        (daseinTrace.map (fun s => normMod8Of s.shape))[t₂]? := by
  rw [walk_normMod8]
  simp only [phaseIntervals, List.mem_cons, List.not_mem_nil, or_false]
  rintro I (rfl | rfl | rfl | rfl)
  · exact ⟨0, 3, by decide +kernel⟩
  · exact ⟨255, 263, by decide +kernel⟩
  · exact ⟨314, 315, by decide +kernel⟩
  · exact ⟨421, 430, by decide +kernel⟩

end Dasein15VM
