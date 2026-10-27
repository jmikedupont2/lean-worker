import RequestProject.Dasein15VM.MonsterWalk.Core
import RequestProject.Dasein15VM.Shape

/-!
# Audit of the numerical data of `MonsterWalkZKP` (REQ-0001 item 7)

* `monsterExponents` really is the factorisation of the Monster's order:
  `godel_monsterExponents` evaluates `∏ p_i ^ e_i` to
  `808017424794512875886459904961710757005754368000000000`.
* `MonsterScore` is computed rather than asserted: `scoreOf v` = (number of nonzero exponents,
  least nonzero exponent, largest exponent). `scoreOf_monster`, `scoreOf_baby`, `scoreOf_fi24`
  recover `monsterSelfScore`, `babyMonsterScore`, `fi24Score` from the exponent vectors of
  `|M|`, `|B|` and `|Fi24'|` (whose products are evaluated in `godel_babyExponents`,
  `godel_fi24Exponents`).
* `irrepDim`:
  - the three listed nontrivial dimensions divide `|M|` (`irrepDim_dvd_monster_order`), as the
    dimension of an irreducible complex representation of a finite group must;
  - `irrepDim k = 0` for `k ≥ 4` (`irrepDim_vanishes`), which is not the dimension of any
    representation — `irrepDim` is a table of the first four dimensions, not a dimension function;
  - "196883 is the smallest useful program" has no formal metric behind it; the only formal content
    is `irrepDim_one_least`: among the listed nontrivial dimensions, `196883` is the least.
  - `trivector_eq_irrepDim`: `47 · 59 · 71 = irrepDim 1` (arithmetic coincidence, as stated).
-/

namespace MonsterWalkZKP

open Dasein15VM

/-- The computed score of an exponent vector. -/
def scoreOf (v : ExponentVector) : MonsterScore where
  support := ((List.finRange 15).filter fun i => v i ≠ 0).length
  floor := (((List.finRange 15).filter fun i => v i ≠ 0).map v).min?.getD 0
  steep := ((List.finRange 15).map v).max?.getD 0

/-- Exponent vector of `|B| = 2^41 3^13 5^6 7^2 11 13 17 19 23 31 47`. -/
def babyExponents : ExponentVector := ![41, 13, 6, 2, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0]

/-- Exponent vector of `|Fi24'| = 2^21 3^16 5^2 7^3 11 13 17 23 29`. -/
def fi24Exponents : ExponentVector := ![21, 16, 2, 3, 1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0]

theorem godel_monsterExponents :
    godel sspBasis monsterExponents = 808017424794512875886459904961710757005754368000000000 := by
  decide +kernel

theorem godel_babyExponents :
    godel sspBasis babyExponents = 4154781481226426191177580544000000 := by
  decide +kernel

theorem godel_fi24Exponents : godel sspBasis fi24Exponents = 1255205709190661721292800 := by
  decide +kernel

theorem scoreOf_monster : scoreOf monsterExponents = monsterSelfScore := by decide +kernel
theorem scoreOf_baby : scoreOf babyExponents = babyMonsterScore := by decide +kernel
theorem scoreOf_fi24 : scoreOf fi24Exponents = fi24Score := by decide +kernel

/-- The listed nontrivial irreducible dimensions divide the Monster's order. -/
theorem irrepDim_dvd_monster_order :
    ∀ k ∈ [1, 2, 3], irrepDim k ∣ godel sspBasis monsterExponents := by
  rw [godel_monsterExponents]; decide

/-- `irrepDim` vanishes from index 4 on: it is a finite table, not a dimension function. -/
theorem irrepDim_vanishes (k : ℕ) (hk : 4 ≤ k) : irrepDim k = 0 := by
  match k, hk with
  | k + 4, _ => rfl

/-- Among the listed nontrivial dimensions, `196883` is the least. -/
theorem irrepDim_one_least (k : ℕ) (hk : 1 ≤ k) (h0 : irrepDim k ≠ 0) :
    irrepDim 1 ≤ irrepDim k := by
  match k, hk, h0 with
  | 1, _, _ => exact le_rfl
  | 2, _, _ => decide
  | 3, _, _ => decide
  | k + 4, _, h => exact absurd rfl h

theorem trivector_eq_irrepDim : (47 : ℕ) * 59 * 71 = irrepDim 1 := rfl

end MonsterWalkZKP
