import RequestProject.Dasein15VM.MonsterWalk.Core

/-!
# Audit of the Ramanujan tau table (REQ-0001 item 7)

`ramanujanTau n` is defined from first principles as the coefficient of `q^n` in
`Δ(q) = q ∏_{k ≥ 1} (1 - q^k)^24` (only the factors with `k ≤ n` can contribute to that
coefficient, so the product is truncated at `k = n`).

The values for the 15 supersingular primes are computed in the kernel (`decide +kernel`) through a
list-based evaluation of the truncated product whose correctness is proved
(`tauList_spec`, `ramanujanTau_eq_tauList`).

Findings:
* `ramanujan_tau_table_wrong`: the table `MonsterWalkZKP.ramanujan_tau` is wrong at
  `p = 29, 31, 41, 59, 71` (signs flipped at 29, 31, 41; wrong values at 59, 71); it is correct
  at the other ten primes (`ramanujan_tau_table_correct`).
* `tau_29_mod24_refuted`: for the true `τ(29) = 128406630`, `τ(29) mod 24 = 6`, not `18`.
* `tau_zero_mod24_primes_genuine`: the set of supersingular primes with `τ(p) ≡ 0 (mod 24)` is
  nevertheless exactly `{2, 23, 47, 71}` for the true values, and the congruences
  `τ(p) ≡ 0 (mod p)` for `p ∈ {2, 3, 5, 7}` hold for the true values.
-/

namespace MonsterWalkZKP

open PowerSeries

/-- The truncated discriminant product `∏_{k < N} (1 - q^(k+1))^24`. -/
noncomputable def deltaProd (N : ℕ) : PowerSeries ℤ :=
  ∏ k ∈ Finset.range N, (1 - X ^ (k + 1)) ^ 24

/-- **Ramanujan's tau function**: the coefficient of `q^n` in `q ∏_{k≥1} (1 - q^k)^24`. -/
noncomputable def ramanujanTau (n : ℕ) : ℤ := coeff n (X * deltaProd n)

/-! ### Stability of the truncation -/

/-- Multiplying by `(1 - X^j)^e` does not change coefficients below `j`. -/
theorem coeff_one_sub_pow_mul (j e : ℕ) (g : PowerSeries ℤ) (i : ℕ) (hi : i < j) :
    coeff i ((1 - X ^ j) ^ e * g) = coeff i g := by
  induction e generalizing g with
  | zero => simp
  | succ e ih =>
    rw [pow_succ, mul_assoc, ih, sub_mul, one_mul, map_sub, coeff_X_pow_mul', if_neg (by omega),
      sub_zero]

theorem coeff_deltaProd_stable (m N : ℕ) (h : m ≤ N) (i : ℕ) (hi : i ≤ m) :
    coeff i (deltaProd N) = coeff i (deltaProd m) := by
  induction N, h using Nat.le_induction with
  | base => rfl
  | succ N hN ih =>
    rw [deltaProd, Finset.prod_range_succ, mul_comm, coeff_one_sub_pow_mul _ _ _ _ (by omega)]
    exact ih

/-- The coefficient of `q^(m+1)` in `Δ` can be read from any truncation with at least `m`
factors. -/
theorem ramanujanTau_succ (m N : ℕ) (h : m ≤ N) :
    ramanujanTau (m + 1) = coeff m (deltaProd N) := by
  rw [ramanujanTau, coeff_succ_X_mul, coeff_deltaProd_stable m (m + 1) (by omega) m le_rfl,
    coeff_deltaProd_stable m N h m le_rfl]

/-! ### Kernel-computable evaluation of the truncated product -/

/-- A coefficient list of length `L` agrees with a power series below degree `L`. -/
def Agrees (L : ℕ) (l : List ℤ) (f : PowerSeries ℤ) : Prop :=
  l.length = L ∧ ∀ i < L, coeff i f = l.getD i 0

/-- Multiply a truncated coefficient list by `1 - X^j`. -/
def mulOneSubXPow (j : ℕ) (l : List ℤ) : List ℤ :=
  List.zipWith (· - ·) l (List.replicate j 0 ++ l)

/-- Coefficients `0, …, L-1` of `∏_{k < N} (1 - q^(k+1))^24`. -/
def deltaList (L N : ℕ) : List ℤ :=
  (List.range N).foldl (fun l k => (mulOneSubXPow (k + 1))^[24] l) (1 :: List.replicate (L - 1) 0)

theorem mulOneSubXPow_spec {L : ℕ} {l : List ℤ} {f : PowerSeries ℤ} (j : ℕ) (h : Agrees L l f) :
    Agrees L (mulOneSubXPow j l) ((1 - X ^ j) * f) := by
  obtain ⟨hl, hc⟩ := h
  refine ⟨by simp [mulOneSubXPow, hl], fun i hi => ?_⟩
  rw [sub_mul, one_mul, map_sub, coeff_X_pow_mul', hc i hi]
  simp only [mulOneSubXPow, List.getD_eq_getElem?_getD, List.getElem?_zipWith,
    List.getElem?_append, List.getElem?_replicate, List.length_replicate]
  have hi' : i < l.length := hl ▸ hi
  rw [List.getElem?_eq_getElem hi']
  by_cases hji : j ≤ i
  · rw [if_pos hji, if_neg (by omega), hc (i - j) (by omega), List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega)]
    rfl
  · simp [hji, show i < j by omega]

theorem iterate_mulOneSubXPow_spec {L : ℕ} (j e : ℕ) :
    ∀ {l : List ℤ} {f : PowerSeries ℤ}, Agrees L l f →
      Agrees L ((mulOneSubXPow j)^[e] l) ((1 - X ^ j) ^ e * f) := by
  induction e with
  | zero => intro l f h; simpa using h
  | succ e ih =>
    intro l f h
    rw [Function.iterate_succ_apply', pow_succ', mul_assoc]
    exact mulOneSubXPow_spec j (ih h)

theorem deltaList_spec (L N : ℕ) (hL : 0 < L) : Agrees L (deltaList L N) (deltaProd N) := by
  induction N with
  | zero =>
    refine ⟨by simp [deltaList]; omega, fun i hi => ?_⟩
    rcases i with _ | i
    · simp [deltaProd, deltaList]
    · simp [deltaProd, deltaList, coeff_one, List.getD_eq_getElem?_getD,
        show i < L - 1 by omega]
  | succ N ih =>
    rw [deltaList, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ← deltaList,
      deltaProd, Finset.prod_range_succ, mul_comm, ← deltaProd]
    exact iterate_mulOneSubXPow_spec _ _ ih

/-- **Correctness of the evaluation**: `τ(m+1)` is entry `m` of the evaluated list. -/
theorem ramanujanTau_eq_deltaList {m L N : ℕ} (hm : m < L) (hN : m ≤ N) :
    ramanujanTau (m + 1) = (deltaList L N).getD m 0 := by
  rw [ramanujanTau_succ m N hN, (deltaList_spec L N (by omega)).2 m hm]

/-- The coefficients of `q^0, …, q^70` of `∏_{k ≤ 70} (1 - q^k)^24`, i.e. `τ(1), …, τ(71)`. -/
def tauValues : List ℤ := [1, -24, 252, -1472, 4830, -6048, -16744, 84480, -113643, -115920, 534612, -370944,
    -577738, 401856, 1217160, 987136, -6905934, 2727432, 10661420, -7109760, -4219488, -12830688,
    18643272, 21288960, -25499225, 13865712, -73279080, 24647168, 128406630, -29211840, -52843168,
    -196706304, 134722224, 165742416, -80873520, 167282496, -182213314, -255874080, -145589976,
    408038400, 308120442, 101267712, -17125708, -786948864, -548895690, -447438528, 2687348496,
    248758272, -1696965207, 611981400, -1740295368, 850430336, -1596055698, 1758697920,
    2582175960, -1414533120, 2686677840, -3081759120, -5189203740, -1791659520, 6956478662,
    1268236032, 1902838392, 2699296768, -2790474540, -3233333376, -15481826884, 10165534848,
    4698104544, 1940964480, 9791485272]

set_option maxRecDepth 100000 in
/-- Kernel evaluation of the truncated discriminant product (no `native_decide`). -/
theorem deltaList_eval : deltaList 71 70 = tauValues := by decide +kernel

theorem ramanujanTau_eq_tauValues {n : ℕ} (h1 : 1 ≤ n) (h2 : n ≤ 71) :
    ramanujanTau n = tauValues.getD (n - 1) 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [ramanujanTau_eq_deltaList (L := 71) (N := 70) (by omega) (by omega), deltaList_eval]
  rfl

/-- The true values of `τ(p)` at the 15 supersingular primes. -/
theorem ramanujanTau_ssp :
    ramanujanTau 2 = -24 ∧ ramanujanTau 3 = 252 ∧ ramanujanTau 5 = 4830 ∧
    ramanujanTau 7 = -16744 ∧ ramanujanTau 11 = 534612 ∧ ramanujanTau 13 = -577738 ∧
    ramanujanTau 17 = -6905934 ∧ ramanujanTau 19 = 10661420 ∧ ramanujanTau 23 = 18643272 ∧
    ramanujanTau 29 = 128406630 ∧ ramanujanTau 31 = -52843168 ∧ ramanujanTau 41 = 308120442 ∧
    ramanujanTau 47 = 2687348496 ∧ ramanujanTau 59 = -5189203740 ∧
    ramanujanTau 71 = 9791485272 := by
  simp only [ramanujanTau_eq_tauValues (by norm_num : 1 ≤ 2) (by norm_num),
    ramanujanTau_eq_tauValues (by norm_num : 1 ≤ 3) (by norm_num),
    ramanujanTau_eq_tauValues (by norm_num : 1 ≤ 5) (by norm_num),
    ramanujanTau_eq_tauValues (by norm_num : 1 ≤ 7) (by norm_num),
    ramanujanTau_eq_tauValues (by norm_num : 1 ≤ 11) (by norm_num),
    ramanujanTau_eq_tauValues (by norm_num : 1 ≤ 13) (by norm_num),
    ramanujanTau_eq_tauValues (by norm_num : 1 ≤ 17) (by norm_num),
    ramanujanTau_eq_tauValues (by norm_num : 1 ≤ 19) (by norm_num),
    ramanujanTau_eq_tauValues (by norm_num : 1 ≤ 23) (by norm_num),
    ramanujanTau_eq_tauValues (by norm_num : 1 ≤ 29) (by norm_num),
    ramanujanTau_eq_tauValues (by norm_num : 1 ≤ 31) (by norm_num),
    ramanujanTau_eq_tauValues (by norm_num : 1 ≤ 41) (by norm_num),
    ramanujanTau_eq_tauValues (by norm_num : 1 ≤ 47) (by norm_num),
    ramanujanTau_eq_tauValues (by norm_num : 1 ≤ 59) (by norm_num),
    ramanujanTau_eq_tauValues (by norm_num : 1 ≤ 71) (by norm_num)]
  decide

/-! ### Audit of `MonsterWalkZKP.ramanujan_tau` -/

/-- The table agrees with the true `τ` at ten of the fifteen supersingular primes. -/
theorem ramanujan_tau_table_correct :
    ∀ p ∈ [2, 3, 5, 7, 11, 13, 17, 19, 23, 47], ramanujan_tau p = ramanujanTau p := by
  obtain ⟨h2, h3, h5, h7, h11, h13, h17, h19, h23, -, -, -, h47, -, -⟩ := ramanujanTau_ssp
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [ramanujan_tau, *]

/-- **Refutation**: the table `MonsterWalkZKP.ramanujan_tau` is wrong at `29, 31, 41, 59, 71`. -/
theorem ramanujan_tau_table_wrong :
    ramanujan_tau 29 ≠ ramanujanTau 29 ∧ ramanujan_tau 31 ≠ ramanujanTau 31 ∧
    ramanujan_tau 41 ≠ ramanujanTau 41 ∧ ramanujan_tau 59 ≠ ramanujanTau 59 ∧
    ramanujan_tau 71 ≠ ramanujanTau 71 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h29, h31, h41, -, h59, h71⟩ := ramanujanTau_ssp
  simp only [h29, h31, h41, h59, h71]
  decide

/-- **Refutation of `tau_29_mod24` for the true tau function**: `τ(29) mod 24 = 6`, not `18`. -/
theorem tau_29_mod24_refuted : ramanujanTau 29 % 24 = 6 ∧ ¬ ramanujanTau 29 % 24 = 18 := by
  rw [ramanujanTau_ssp.2.2.2.2.2.2.2.2.2.1]; decide

/-- The supersingular primes with `τ(p) ≡ 0 (mod 24)`, for the true `τ`, are exactly
`2, 23, 47, 71` (so the conclusion of `tau_zero_mod24_primes` survives the audit). -/
theorem tau_zero_mod24_primes_genuine :
    SSP_list.filter (fun p => ramanujanTau p % 24 = 0) = [2, 23, 47, 71] := by
  obtain ⟨h2, h3, h5, h7, h11, h13, h17, h19, h23, h29, h31, h41, h47, h59, h71⟩ := ramanujanTau_ssp
  simp only [SSP_list, List.filter_cons, List.filter_nil, h2, h3, h5, h7, h11, h13, h17, h19, h23,
    h29, h31, h41, h47, h59, h71]
  decide

/-- The congruences `τ(p) ≡ 0 (mod p)` for `p = 2, 3, 5, 7` hold for the true `τ`. -/
theorem ramanujan_congruence_genuine :
    ramanujanTau 2 % 2 = 0 ∧ ramanujanTau 3 % 3 = 0 ∧ ramanujanTau 5 % 5 = 0 ∧
    ramanujanTau 7 % 7 = 0 := by
  obtain ⟨h2, h3, h5, h7, -⟩ := ramanujanTau_ssp
  rw [h2, h3, h5, h7]; decide

end MonsterWalkZKP
