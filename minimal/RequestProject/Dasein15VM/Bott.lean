import RequestProject.Dasein15VM.Walk

/-!
# Dasein15 VM: the "Bott class" along the walk, computed from the walk itself

`Dasein15.bottClass` is applied to the floor of the Euclidean norm of the exponent vector,
i.e. `⌊‖v‖⌋ mod 8`. Here that quantity is computed for every state of the certified 500-state walk.

* `walk_normFloors`: the norm floors of the walk are the list `walkNormFloors` (each entry is
  certified by `k² ≤ ‖v‖² < (k+1)²`, checked in the kernel).
* `walk_bott_phase_starts`: at the phase starts (steps 0, 255, 314, 421) the classes are 2, 7, 7, 1,
  and at the final step 499 the class is 1 — the values written in `Dasein15.bott_trajectory` and
  `final_bott`.
* `walk_bott_all_values_each_phase`: **within each of the four phases, all 8 classes occur.** So the
  Bott class is not a phase invariant; it is `⌊‖v‖⌋ mod 8`, a number that cycles as the norm moves
  between 34 and 58.
-/

namespace Dasein15VM

open Dasein15

variable {n : ℕ}

/-- Squared Euclidean norm of a shape. -/
def sumSq (v : PrimeShape n) : ℕ := (List.ofFn fun i => v i * v i).sum

/-- Floor of the Euclidean norm of a shape. -/
def normFloor (v : PrimeShape n) : ℕ := Nat.sqrt (sumSq v)

/-- The "Bott class" of a shape: `⌊‖v‖⌋ mod 8`. -/
def bottOf (v : PrimeShape n) : Fin 8 := bottClass (normFloor v)

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

/-- The Bott classes along the walk. -/
theorem walk_bott : daseinTrace.map (fun s => bottOf s.shape) = walkNormFloors.map bottClass := by
  rw [← walk_normFloors, List.map_map]; rfl

/-- Bott classes at the phase starts (steps 0, 255, 314, 421) and at the final step 499. -/
theorem walk_bott_phase_starts :
    [0, 255, 314, 421, 499].map (fun k => (daseinTrace.map (fun s => bottOf s.shape))[k]?) =
      [some 2, some 7, some 7, some 1, some 1] := by
  rw [walk_bott]; decide +kernel

/-- Phase intervals of the walk, `[start, stop)`. -/
def phaseIntervals : List (ℕ × ℕ) := [(0, 255), (255, 314), (314, 421), (421, 500)]

/-- **Within each of the four phases of the walk, every one of the 8 Bott classes occurs.** -/
theorem walk_bott_all_values_each_phase :
    ∀ I ∈ phaseIntervals, ∀ b : Fin 8,
      b ∈ ((daseinTrace.map (fun s => bottOf s.shape)).take I.2).drop I.1 := by
  rw [walk_bott]; decide +kernel

end Dasein15VM
