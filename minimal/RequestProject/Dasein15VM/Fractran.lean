import RequestProject.Dasein15VM.Shape

/-!
# Dasein15 VM: FRACTRAN semantics and routed transitions

* `fractranStep prog c`: one standard FRACTRAN step (first fraction `f` of `prog` with `c * f`
  an integer); `fractranRun prog k c` iterates it `k` times.
* A *route* `τ : Fin n → Fin n` describes a FRACTRAN program `routeProg B τ` whose `i`-th
  fraction is `p (τ i) / p i`.  Dasein15's cyclic elevator `daseinFrac` is the route `i ↦ i + 1`
  (`routeProg_elevator`).
* `routeStep τ v`: the same transition on exponent vectors — move one unit of mass from the first
  occupied coordinate `i` to `τ i`.
* `fractranStep_routeProg`: for a fixed-point-free route, a FRACTRAN step on a Gödel number is
  exactly `routeStep` on its shape.  `mass_routeStep`: routed steps conserve mass.
-/

namespace Dasein15VM

open Dasein15

variable {n : ℕ}

/-- One FRACTRAN step: apply the first fraction producing an integer; `none` = halt. -/
def fractranStep : List ℚ → ℕ → Option ℕ
  | [], _ => none
  | f :: fs, c => if ((c : ℚ) * f).den = 1 then some ((c : ℚ) * f).num.toNat else fractranStep fs c

/-- `k` FRACTRAN steps (`none` if the program halts earlier). -/
def fractranRun (prog : List ℚ) : ℕ → ℕ → Option ℕ
  | 0, c => some c
  | k + 1, c => (fractranStep prog c).bind (fractranRun prog k)

/-- First occupied coordinate of a shape. -/
def firstPos (v : PrimeShape n) : Option (Fin n) := (List.finRange n).find? fun i => 0 < v i

/-- Move one unit of mass from coordinate `i` to coordinate `j`. -/
def moveUnit (v : PrimeShape n) (i j : Fin n) : PrimeShape n :=
  Function.update (Function.update v i (v i - 1)) j (Function.update v i (v i - 1) j + 1)

/-- The routed transition on shapes. -/
def routeStep (τ : Fin n → Fin n) (v : PrimeShape n) : Option (PrimeShape n) :=
  (firstPos v).map fun i => moveUnit v i (τ i)

/-- The FRACTRAN program of a route: fractions `p (τ i) / p i` in index order. -/
def routeProg (B : PrimeBasis n) (τ : Fin n → Fin n) : List ℚ :=
  (List.finRange n).map fun i => (B.p (τ i) : ℚ) / B.p i

theorem sum_update_add (w : PrimeShape n) (k : Fin n) (e : ℕ) :
    (∑ l, Function.update w k e l) + w k = (∑ l, w l) + e := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k),
    ← Finset.add_sum_erase _ (fun l => w l) (Finset.mem_univ k)]
  rw [Finset.sum_congr rfl fun l hl => by
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]]
  simp only [Function.update_self]; ring

theorem prod_update_mul (B : PrimeBasis n) (w : PrimeShape n) (k : Fin n) (e : ℕ) :
    (∏ l, B.p l ^ Function.update w k e l) * B.p k ^ w k = (∏ l, B.p l ^ w l) * B.p k ^ e := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k),
    ← Finset.mul_prod_erase _ (fun l => B.p l ^ w l) (Finset.mem_univ k)]
  rw [Finset.prod_congr rfl fun l hl => by
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]]
  simp only [Function.update_self]; ring

theorem mass_moveUnit (v : PrimeShape n) {i : Fin n} (j : Fin n) (h : 0 < v i) :
    mass (moveUnit v i j) = mass v := by
  simp only [mass_eq_sum, moveUnit]
  have k1 := sum_update_add v i (v i - 1)
  have k2 := sum_update_add (Function.update v i (v i - 1)) j
    (Function.update v i (v i - 1) j + 1)
  omega

theorem godel_moveUnit (B : PrimeBasis n) (v : PrimeShape n) {i : Fin n} (j : Fin n)
    (h : 0 < v i) : godel B (moveUnit v i j) * B.p i = godel B v * B.p j := by
  simp only [godel_eq_prod, moveUnit]
  have k1 := prod_update_mul B v i (v i - 1)
  have k2 := prod_update_mul B (Function.update v i (v i - 1)) j
    (Function.update v i (v i - 1) j + 1)
  generalize Function.update v i (v i - 1) = w at k1 k2 ⊢
  generalize ∏ l, B.p l ^ Function.update w j (w j + 1) l = P2 at k2 ⊢
  generalize ∏ l, B.p l ^ w l = P1 at k1 k2
  generalize ∏ l, B.p l ^ v l = P0 at k1 ⊢
  obtain ⟨m, hm⟩ : ∃ m, v i = m + 1 := ⟨v i - 1, by omega⟩
  rw [hm, Nat.add_sub_cancel, pow_succ] at k1
  rw [pow_succ] at k2
  have e1 : P1 * B.p i = P0 :=
    Nat.eq_of_mul_eq_mul_right (pow_pos (B.prime i).pos m)
      (by calc _ = P1 * (B.p i ^ m * B.p i) := by ring
            _ = _ := k1)
  have e2 : P2 = P1 * B.p j :=
    Nat.eq_of_mul_eq_mul_right (pow_pos (B.prime j).pos (w j))
      (by calc _ = P1 * (B.p j ^ w j * B.p j) := k2
            _ = _ := by ring)
  rw [e2, ← e1]; ring

/-- Whether a route fraction applies, and what it produces. -/
theorem fractranFrac_godel (B : PrimeBasis n) (v : PrimeShape n) {i j : Fin n} (hij : j ≠ i) :
    (((godel B v : ℕ) : ℚ) * ((B.p j : ℚ) / B.p i)).den = 1 ↔ 0 < v i := by
  constructor
  · intro hden
    by_contra hv
    push_neg at hv
    set q : ℚ := ((godel B v : ℕ) : ℚ) * ((B.p j : ℚ) / B.p i)
    have hpi : (B.p i : ℚ) ≠ 0 := by exact_mod_cast (B.prime i).ne_zero
    have hq : (q.num : ℚ) * B.p i = (godel B v * B.p j : ℕ) := by
      rw [Rat.coe_int_num_of_den_eq_one hden]
      simp only [q]; push_cast; field_simp
    have hz : q.num * (B.p i : ℤ) = ((godel B v * B.p j : ℕ) : ℤ) := by exact_mod_cast hq
    have hdvd : B.p i ∣ godel B v * B.p j := by
      have : (B.p i : ℤ) ∣ ((godel B v * B.p j : ℕ) : ℤ) := ⟨q.num, by rw [← hz]; ring⟩
      exact_mod_cast this
    rcases (Nat.Prime.dvd_mul (B.prime i)).1 hdvd with h | h
    · exact absurd ((dvd_godel_iff B v i).1 h) (by omega)
    · have := (Nat.prime_dvd_prime_iff_eq (B.prime i) (B.prime j)).1 h
      exact hij (B.injective this).symm
  · intro h
    have e := godel_moveUnit B v j h
    have : ((godel B v : ℕ) : ℚ) * ((B.p j : ℚ) / B.p i) = (godel B (moveUnit v i j) : ℕ) := by
      have hpi : (B.p i : ℚ) ≠ 0 := by exact_mod_cast (B.prime i).ne_zero
      field_simp
      rw [mul_comm (B.p i : ℚ)]
      exact_mod_cast e.symm
    rw [this]; rfl

theorem fractranFrac_godel_val (B : PrimeBasis n) (v : PrimeShape n) {i : Fin n} (j : Fin n)
    (h : 0 < v i) :
    (((godel B v : ℕ) : ℚ) * ((B.p j : ℚ) / B.p i)).num.toNat = godel B (moveUnit v i j) := by
  have e := godel_moveUnit B v j h
  have : ((godel B v : ℕ) : ℚ) * ((B.p j : ℚ) / B.p i) = (godel B (moveUnit v i j) : ℕ) := by
    have hpi : (B.p i : ℚ) ≠ 0 := by exact_mod_cast (B.prime i).ne_zero
    field_simp
    rw [mul_comm (B.p i : ℚ)]
    exact_mod_cast e.symm
  rw [this]; simp

/-- List-generic form of the FRACTRAN bridge. -/
theorem fractranStep_map_godel (B : PrimeBasis n) (τ : Fin n → Fin n) (hτ : ∀ i, τ i ≠ i)
    (v : PrimeShape n) (L : List (Fin n)) :
    fractranStep (L.map fun i => (B.p (τ i) : ℚ) / B.p i) (godel B v) =
      (L.find? fun i => 0 < v i).map fun i => godel B (moveUnit v i (τ i)) := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    simp only [List.map_cons, fractranStep, List.find?_cons]
    by_cases h : 0 < v i
    · rw [if_pos ((fractranFrac_godel B v (hτ i)).2 h), fractranFrac_godel_val B v _ h]
      simp [h]
    · rw [if_neg (mt (fractranFrac_godel B v (hτ i)).1 h), ih]
      simp [h]

/-- **FRACTRAN bridge.** For a fixed-point-free route, one FRACTRAN step of `routeProg B τ` on the
Gödel number of `v` is the Gödel number of `routeStep τ v`. -/
theorem fractranStep_routeProg (B : PrimeBasis n) (τ : Fin n → Fin n) (hτ : ∀ i, τ i ≠ i)
    (v : PrimeShape n) :
    fractranStep (routeProg B τ) (godel B v) = (routeStep τ v).map (godel B) := by
  rw [routeProg, fractranStep_map_godel B τ hτ, routeStep, firstPos, Option.map_map]
  rfl

/-- Routed steps conserve mass. -/
theorem mass_routeStep (τ : Fin n → Fin n) {v w : PrimeShape n} (h : routeStep τ v = some w) :
    mass w = mass v := by
  simp only [routeStep, Option.map_eq_some_iff, firstPos] at h
  obtain ⟨i, hi, rfl⟩ := h
  have := List.find?_some hi
  exact mass_moveUnit v _ (by simpa using this)

/-- A routed step only halts on the empty shape. -/
theorem routeStep_isSome (τ : Fin n → Fin n) {v : PrimeShape n} (h : 0 < mass v) :
    (routeStep τ v).isSome := by
  rw [mass_eq_sum] at h
  obtain ⟨i, -, hi⟩ := Finset.exists_lt_of_sum_lt (s := Finset.univ) (f := fun _ => 0)
    (g := v) (by simpa using h)
  simp only [routeStep, Option.isSome_map, firstPos, List.find?_isSome]
  exact ⟨i, List.mem_finRange i, by simpa using hi⟩

/-- Dasein15's cyclic elevator route `i ↦ i + 1` (mod 15). -/
def elevator : Fin 15 → Fin 15 := fun i => i + 1

theorem elevator_ne (i : Fin 15) : elevator i ≠ i := by revert i; decide

/-- The FRACTRAN program of the elevator route is exactly Dasein15's `daseinFrac` program. -/
theorem routeProg_elevator : routeProg sspBasis elevator = List.ofFn daseinFrac := by
  rw [routeProg, List.ofFn_eq_map]
  congr 1
  funext i
  fin_cases i <;> simp [daseinFrac, elevator, sspBasis, SSP]

end Dasein15VM
