module

public import Mathlib

/-!
# SpectrumVM §4/§5: factored orders and order-certificate soundness (K1, K2)

Raw wire format `RawFactoredOrder` versus the validated type `ValidFactoredOrder` (review §6).
The checker `checkFactorization` is a `Bool` function; its soundness theorem shows that a passing
certificate lists **exactly** the prime divisors of `val`, with the correct exponents, and that
`val > 0` (review §5).
-/

@[expose] public section

namespace SpectrumVM

/-- Kernel-friendly primality test by trial division. -/
def isPrimeB (p : ℕ) : Bool :=
  decide (2 ≤ p) && (List.range p).all fun d => decide (d < 2) || p % d != 0

theorem isPrimeB_iff (p : ℕ) : isPrimeB p = true ↔ p.Prime := by
  rw [Nat.prime_def_lt]
  simp only [isPrimeB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨h2, h⟩
    refine ⟨h2, fun m hm hdvd => ?_⟩
    rcases h m hm with h' | h'
    · have h' : m < 2 := by simpa using h'
      interval_cases m
      · simp at hdvd; omega
      · rfl
    · exact absurd (Nat.mod_eq_zero_of_dvd hdvd) h'
  · rintro ⟨h2, h⟩
    refine ⟨h2, fun d hd => ?_⟩
    by_cases hd2 : d < 2
    · exact Or.inl (by simpa using hd2)
    · right
      intro hmod
      have := h d hd (Nat.dvd_of_mod_eq_zero hmod)
      omega

/-- Raw (unvalidated) sparse prime factorization: a list of `(p, e)` and a claimed value. -/
structure RawFactoredOrder where
  fac : List (ℕ × ℕ)
  val : ℕ
  deriving DecidableEq, Repr

/-- `facOK b l`: the primes of `l` are prime, strictly increasing and all `> b`, and every exponent
is positive. -/
def facOK : ℕ → List (ℕ × ℕ) → Bool
  | _, [] => true
  | b, (p, e) :: t => decide (b < p) && isPrimeB p && decide (0 < e) && facOK p t

/-- The value denoted by a factor list: `∏ p ^ e`. -/
def facProd (l : List (ℕ × ℕ)) : ℕ := (l.map fun pe => pe.1 ^ pe.2).prod

/-- **K2 checker.** Every listed `p` is prime, exponents are positive, primes strictly increase,
and the product equals `val`. -/
def checkFactorization (f : RawFactoredOrder) : Bool :=
  facOK 0 f.fac && facProd f.fac == f.val

/-- Validated factored order (proof-carrying). -/
structure ValidFactoredOrder extends RawFactoredOrder where
  valid : checkFactorization toRawFactoredOrder = true

theorem facProd_cons (p e : ℕ) (t : List (ℕ × ℕ)) : facProd ((p, e) :: t) = p ^ e * facProd t := by
  simp [facProd]

theorem facOK_cons {b p e : ℕ} {t : List (ℕ × ℕ)} :
    facOK b ((p, e) :: t) = true ↔ b < p ∧ p.Prime ∧ 0 < e ∧ facOK p t = true := by
  simp [facOK, isPrimeB_iff, and_assoc]

theorem facOK_lt {b : ℕ} {l : List (ℕ × ℕ)} (h : facOK b l = true) :
    ∀ pe ∈ l, b < pe.1 ∧ pe.1.Prime := by
  induction l generalizing b with
  | nil => simp
  | cons pe t ih =>
    obtain ⟨p, e⟩ := pe
    rw [facOK_cons] at h
    obtain ⟨hb, hp, -, ht⟩ := h
    intro qe hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact ⟨hb, hp⟩
    · have := ih ht qe hq; exact ⟨by omega, this.2⟩

theorem facProd_pos (l : List (ℕ × ℕ)) {b : ℕ} (h : facOK b l = true) : 0 < facProd l := by
  induction l generalizing b with
  | nil => simp [facProd]
  | cons pe t ih =>
    obtain ⟨p, e⟩ := pe
    rw [facOK_cons] at h
    rw [facProd_cons]
    exact Nat.mul_pos (pow_pos h.2.1.pos _) (ih h.2.2.2)

theorem prime_dvd_facProd_iff {b : ℕ} {l : List (ℕ × ℕ)} (h : facOK b l = true) {q : ℕ}
    (hq : q.Prime) : q ∣ facProd l ↔ q ∈ l.map Prod.fst := by
  induction l generalizing b with
  | nil => simp [facProd, hq.ne_one]
  | cons pe t ih =>
    obtain ⟨p, e⟩ := pe
    rw [facOK_cons] at h
    obtain ⟨-, hp, he, ht⟩ := h
    rw [facProd_cons, hq.dvd_mul, ih ht]
    simp only [List.map_cons, List.mem_cons]
    constructor
    · rintro (h | h)
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow h))
      · exact Or.inr h
    · rintro (rfl | h)
      · exact Or.inl (dvd_pow_self _ (by omega))
      · exact Or.inr h

theorem factorization_facProd {b : ℕ} {l : List (ℕ × ℕ)} (h : facOK b l = true) :
    ∀ pe ∈ l, (facProd l).factorization pe.1 = pe.2 := by
  induction l generalizing b with
  | nil => simp
  | cons pe t ih =>
    obtain ⟨p, e⟩ := pe
    have h' := h
    rw [facOK_cons] at h
    obtain ⟨-, hp, he, ht⟩ := h
    have hpos := facProd_pos t ht
    intro qe hqe
    rw [facProd_cons, Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hpos.ne',
      Finsupp.add_apply, hp.factorization_pow, Finsupp.single_apply]
    rcases List.mem_cons.mp hqe with rfl | hqe
    · simp only [if_true]
      have : ¬ p ∣ facProd t := by
        rw [prime_dvd_facProd_iff ht hp]
        intro hm
        obtain ⟨x, hx, hxp⟩ := List.mem_map.mp hm
        have := (facOK_lt ht x hx).1
        omega
      rw [Nat.factorization_eq_zero_of_not_dvd this, add_zero]
    · have hlt := (facOK_lt ht qe hqe).1
      rw [if_neg (by omega), ih ht qe hqe, zero_add]

/-- **K2 soundness.** A passing factorization certificate has positive value, lists exactly the
prime divisors of `val`, and lists each with its exact multiplicity. -/
theorem checkFactorization_sound {f : RawFactoredOrder} (h : checkFactorization f = true) :
    0 < f.val ∧ (∀ q : ℕ, q.Prime → (q ∣ f.val ↔ q ∈ f.fac.map Prod.fst)) ∧
      (∀ pe ∈ f.fac, pe.1.Prime ∧ f.val.factorization pe.1 = pe.2) := by
  simp only [checkFactorization, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hok, hprod⟩ := h
  rw [← hprod]
  exact ⟨facProd_pos _ hok, fun q hq => prime_dvd_facProd_iff hok hq,
    fun pe hpe => ⟨(facOK_lt hok pe hpe).2, factorization_facProd hok pe hpe⟩⟩

theorem ValidFactoredOrder.val_pos (f : ValidFactoredOrder) : 0 < f.val :=
  (checkFactorization_sound f.valid).1

/-- **K1 (order certificate soundness), Mathlib form.** -/
theorem orderOf_eq_of_pow_cert {M : Type*} [Monoid M] {x : M} {m : ℕ} (hm : 0 < m)
    (h1 : x ^ m = 1) (h2 : ∀ p : ℕ, p.Prime → p ∣ m → x ^ (m / p) ≠ 1) : orderOf x = m :=
  orderOf_eq_of_pow_and_pow_div_prime hm h1 h2

/-- **K1 + K2.** With a validated factorization, the "for every prime `p ∣ n`" quantifier of K1
reduces to the finitely many listed primes. -/
theorem orderOf_eq_of_factored {M : Type*} [Monoid M] {x : M} (f : RawFactoredOrder)
    (hf : checkFactorization f = true) (h1 : x ^ f.val = 1)
    (h2 : ∀ pe ∈ f.fac, x ^ (f.val / pe.1) ≠ 1) : orderOf x = f.val := by
  obtain ⟨hpos, hdiv, -⟩ := checkFactorization_sound hf
  refine orderOf_eq_of_pow_and_pow_div_prime hpos h1 fun p hp hpd => ?_
  obtain ⟨pe, hpe, rfl⟩ := List.mem_map.mp ((hdiv p hp).mp hpd)
  exact h2 pe hpe

/-! ### K2 negative tests (RFC §12) -/

/-- Missing prime divisor: `12` listed as `2^2` only. -/
example : checkFactorization ⟨[(2, 2)], 12⟩ = false := by decide
/-- Composite listed as prime: `12 = 4 * 3`. -/
example : checkFactorization ⟨[(3, 1), (4, 1)], 12⟩ = false := by decide
/-- Wrong exponent: `12` listed as `2 * 3`. -/
example : checkFactorization ⟨[(2, 1), (3, 1)], 12⟩ = false := by decide
/-- Primes out of order. -/
example : checkFactorization ⟨[(3, 1), (2, 2)], 12⟩ = false := by decide
/-- Zero exponent. -/
example : checkFactorization ⟨[(2, 2), (3, 1), (5, 0)], 12⟩ = false := by decide
/-- `val = 0` is rejected. -/
example : checkFactorization ⟨[], 0⟩ = false := by decide
/-- A valid certificate. -/
example : checkFactorization ⟨[(2, 2), (3, 1)], 12⟩ = true := by decide

end SpectrumVM

end
