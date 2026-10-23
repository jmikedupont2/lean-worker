import RequestProject.Dasein15VM.Fractran

/-!
# Cryptids, part 2: the duel (a one-fraction FRACTRAN comparator)

The *duel* of two primes `p ≠ q` is the one-fraction program `[1 / (p q)]`.  Each step cancels one
`p` against one `q`.  On `p^a q^b c` (with `c` free of `p` and `q`) it runs for exactly
`min a b` steps and halts on `p^(a - b) q^(b - a) c` (truncated subtraction): the survivor tells
which exponent was larger, and by how much — a three-valued comparison computed by FRACTRAN.
-/

namespace Dasein15VM.Cryptids

open Dasein15VM

/-- The duel program of `p` and `q`. -/
def duelProg (p q : ℕ) : List ℚ := [(1 : ℚ) / ((p * q : ℕ) : ℚ)]

theorem fractranStep_duel (p q c : ℕ) (hpq : p * q ≠ 0) :
    fractranStep (duelProg p q) c = if p * q ∣ c then some (c / (p * q)) else none := by
  have e : ((c : ℚ) * ((1 : ℚ) / ((p * q : ℕ) : ℚ))) = (c : ℚ) / ((p * q : ℕ) : ℚ) := by ring
  simp only [duelProg, fractranStep, e, Rat.den_div_natCast_eq_one_iff c _ hpq]
  split_ifs with h
  · obtain ⟨k, rfl⟩ := h
    have hq : ((p * q : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hpq
    rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hpq)]
    push_cast
    rw [mul_div_cancel_left₀ _ (by exact_mod_cast hpq)]
    simp
  · rfl

variable {p q : ℕ}

/-- **Duel run**: `min a b` steps cancel the common part. -/
theorem duel_run (hp : p.Prime) (hq : q.Prime) (c : ℕ) :
    ∀ a b : ℕ, fractranRun (duelProg p q) (min a b) (p ^ a * q ^ b * c) =
      some (p ^ (a - b) * q ^ (b - a) * c)
  | 0, b => by simp [fractranRun]
  | a + 1, 0 => by simp [fractranRun]
  | a + 1, b + 1 => by
    have hpq : p * q ≠ 0 := Nat.mul_ne_zero hp.ne_zero hq.ne_zero
    have e : p ^ (a + 1) * q ^ (b + 1) * c = p * q * (p ^ a * q ^ b * c) := by ring
    rw [show min (a + 1) (b + 1) = min a b + 1 by omega, fractranRun,
      fractranStep_duel _ _ _ hpq, e,
      if_pos (dvd_mul_right _ _), Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hpq),
      Option.bind_some, duel_run hp hq c a b]
    simp

/-- **Duel halting**: the survivor is stuck. -/
theorem duel_halts (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {c : ℕ} (hpc : ¬ p ∣ c)
    (hqc : ¬ q ∣ c) (a b : ℕ) :
    fractranStep (duelProg p q) (p ^ (a - b) * q ^ (b - a) * c) = none := by
  rw [fractranStep_duel _ _ _ (Nat.mul_ne_zero hp.ne_zero hq.ne_zero), if_neg]
  intro h
  have hp' : p ∣ p ^ (a - b) * q ^ (b - a) * c := (dvd_mul_right p q).trans h
  have hq' : q ∣ p ^ (a - b) * q ^ (b - a) * c := (dvd_mul_left q p).trans h
  have hqp : ¬ q ∣ p := fun h => hpq ((Nat.prime_dvd_prime_iff_eq hq hp).1 h).symm
  have hpq' : ¬ p ∣ q := fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp hq).1 h)
  rcases le_total a b with hab | hab
  · rw [Nat.sub_eq_zero_of_le hab] at hp'
    simp only [pow_zero, one_mul] at hp'
    rcases (Nat.Prime.dvd_mul hp).1 hp' with h1 | h1
    · exact hpq' (hp.dvd_of_dvd_pow h1)
    · exact hpc h1
  · rw [Nat.sub_eq_zero_of_le hab] at hq'
    simp only [pow_zero, mul_one] at hq'
    rcases (Nat.Prime.dvd_mul hq).1 hq' with h1 | h1
    · exact hqp (hq.dvd_of_dvd_pow h1)
    · exact hqc h1

end Dasein15VM.Cryptids
