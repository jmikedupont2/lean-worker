module

public import RequestProject.SpectrumVM.SmallTypes
public import RequestProject.SpectrumVM.Exceptional

/-!
# SpectrumVM §6.2: concrete rewriting-transversal certificates and sharded assembly

A `RawCosetCert` lists representative words `r_a`, the generators of the subgroup `H` (a subset of
the simple reflections), a vector `λ`, and rewrites `(j, a, b, h)` meaning `s_j r_a = r_b h` with `h`
a word in the `H` generators.  `checkCosetCert` replays the five checks of RFC rev. 2 §6.2:

1. some representative evaluates to the identity;
2. all words evaluate (by construction) and every `h` uses only `H` generators;
3. every rewriting identity holds exactly, for every generator `j` and representative `a`;
4. `λ` is fixed by every generator of `H`;
5. the images `r_a λ` are pairwise distinct.

Soundness: `checkCosetCert_cover` (every word matrix is `r_a h`) and `checkCosetCert_disjoint`
(distinct cosets).  `checkCosetBundle_sound` assembles a coset certificate, a closure certificate for
`H` and one order shard per coset into the exact spectrum, with no stabilizer theorem.  The
mechanism is exercised on `W(A₃) = ⋃ r_a W(A₂)` (index 4), together with the negative tests of RFC
§12.  The concrete `E₈` instance (240 cosets) has not been run.
-/

@[expose] public section

namespace SpectrumVM

open Matrix

variable {n : ℕ}

/-! ### List vectors -/

def toVec (n : ℕ) (v : List ℤ) : Fin n → ℤ := fun i => v.getD i 0

def lmulVec (n : ℕ) (A : LMat) (v : List ℤ) : List ℤ :=
  (List.range n).map fun i => ((List.range n).map fun k => lget A i k * v.getD k 0).sum

def lvecEq (n : ℕ) (v w : List ℤ) : Bool := (List.range n).all fun i => v.getD i 0 == w.getD i 0

theorem toVec_lmulVec (A : LMat) (v : List ℤ) :
    toVec n (lmulVec n A v) = toMat n A *ᵥ toVec n v := by
  ext i
  simp only [toVec, lmulVec, mulVec, dotProduct, toMat]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range i.isLt]
  simp only [Option.map_some, Option.getD_some]
  rw [Fin.sum_univ_eq_sum_range (fun k => lget A i k * v.getD k 0) n]
  rfl

theorem lvecEq_iff (v w : List ℤ) : lvecEq n v w = true ↔ toVec n v = toVec n w := by
  simp only [lvecEq, List.all_eq_true, List.mem_range, beq_iff_eq]
  constructor
  · intro h; ext i; exact h i i.isLt
  · intro h i hi; exact congrFun h ⟨i, hi⟩

/-! ### Coset certificates -/

/-- Raw rewriting-transversal certificate. -/
structure RawCosetCert (n : ℕ) where
  reps : List (Word n)
  hgens : List (Fin n)
  lam : List ℤ
  rewrites : List (Fin n × ℕ × ℕ × Word n)

def RawCosetCert.rep (c : RawCosetCert n) (a : ℕ) : Word n := c.reps.getD a []

/-- `(a, b)` pairs with `a < b < len`. -/
def lowerPairs (len : ℕ) : List (ℕ × ℕ) :=
  (List.range len).flatMap fun a => ((List.range len).filter (a < ·)).map fun b => (a, b)

theorem mem_lowerPairs {len a b : ℕ} : (a, b) ∈ lowerPairs len ↔ a < b ∧ b < len := by
  simp only [lowerPairs, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter,
    decide_eq_true_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨a', -, b', ⟨hb', hab'⟩, rfl, rfl⟩; exact ⟨hab', hb'⟩
  · rintro ⟨hab, hb⟩; exact ⟨a, by omega, b, ⟨hb, hab⟩, rfl, rfl⟩

/-- **COSET.CHECK**: replay of a rewriting-transversal certificate. -/
def checkCosetCert (R : RootDatum n) (c : RawCosetCert n) : Bool :=
  let len := c.reps.length
  -- (1) identity representative
  (List.range len).any (fun a => lisOne n (lword R (c.rep a))) &&
  -- (2, 3) rewrites for every generator and representative
  (List.finRange n).all (fun j => (List.range len).all fun a =>
    c.rewrites.any fun e => decide (e.1 = j) && decide (e.2.1 = a) && decide (e.2.2.1 < len) &&
      e.2.2.2.all (fun i => decide (i ∈ c.hgens)) &&
      lisEq n (lword R (j :: c.rep a)) (lword R (c.rep e.2.2.1 ++ e.2.2.2))) &&
  -- (4) λ fixed by H generators
  c.hgens.all (fun g => lvecEq n (lmulVec n (lrefl R g) c.lam) c.lam) &&
  -- (5) distinct images
  (lowerPairs len).all fun p =>
    !lvecEq n (lmulVec n (lword R (c.rep p.1)) c.lam) (lmulVec n (lword R (c.rep p.2)) c.lam)

theorem wordMat_fix_of_hgens {R : RootDatum n} {c : RawCosetCert n}
    (hfix : ∀ g ∈ c.hgens, refl R g *ᵥ toVec n c.lam = toVec n c.lam) :
    ∀ u : Word n, (∀ i ∈ u, i ∈ c.hgens) → wordMat R u *ᵥ toVec n c.lam = toVec n c.lam := by
  intro u hu
  induction u with
  | nil => simp
  | cons i u ih =>
    rw [wordMat_cons, ← mulVec_mulVec, ih fun k hk => hu k (List.mem_cons_of_mem i hk),
      hfix i (hu i List.mem_cons_self)]

theorem checkCosetCert_spec {R : RootDatum n} {c : RawCosetCert n}
    (h : checkCosetCert R c = true) :
    (∃ a < c.reps.length, wordMat R (c.rep a) = 1) ∧
    (∀ j : Fin n, ∀ a < c.reps.length, ∃ b < c.reps.length, ∃ u : Word n,
      (∀ i ∈ u, i ∈ c.hgens) ∧ refl R j * wordMat R (c.rep a) = wordMat R (c.rep b) * wordMat R u) ∧
    (∀ g ∈ c.hgens, refl R g *ᵥ toVec n c.lam = toVec n c.lam) ∧
    (∀ a b, a < b → b < c.reps.length →
      wordMat R (c.rep a) *ᵥ toVec n c.lam ≠ wordMat R (c.rep b) *ᵥ toVec n c.lam) := by
  simp only [checkCosetCert, Bool.and_eq_true, List.any_eq_true, List.all_eq_true,
    List.mem_range, List.mem_finRange, forall_const, decide_eq_true_eq,
    Bool.not_eq_eq_eq_not, Bool.not_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, h1⟩ := h1
    exact ⟨a, ha, by rw [← toMat_lword, ← lisOne_iff]; exact h1⟩
  · intro j a ha
    obtain ⟨⟨j', a', b, u⟩, -, ⟨⟨⟨⟨rfl, rfl⟩, hb⟩, hu⟩, heq⟩⟩ := h2 j a ha
    refine ⟨b, hb, u, hu, ?_⟩
    rw [lisEq_iff, toMat_lword, toMat_lword, wordMat_cons, wordMat_append] at heq
    exact heq
  · intro g hg
    have := h3 g hg
    rw [lvecEq_iff, toVec_lmulVec, toMat_lrefl] at this
    exact this
  · intro a b hab hb heq
    have := h4 (a, b) (mem_lowerPairs.mpr ⟨hab, hb⟩)
    rw [← toMat_lword, ← toMat_lword, ← toVec_lmulVec, ← toVec_lmulVec, ← lvecEq_iff] at heq
    rw [heq] at this
    exact absurd this (by decide)

/-- **Coset cover.** Every word matrix is `r_a h` with `h` a word in the `H` generators. -/
theorem checkCosetCert_cover {R : RootDatum n} {c : RawCosetCert n}
    (h : checkCosetCert R c = true) (w : Word n) :
    ∃ a < c.reps.length, ∃ u : Word n, (∀ i ∈ u, i ∈ c.hgens) ∧
      wordMat R w = wordMat R (c.rep a) * wordMat R u := by
  obtain ⟨⟨a₀, ha₀, h1⟩, hrw, -, -⟩ := checkCosetCert_spec h
  induction w with
  | nil => exact ⟨a₀, ha₀, [], by simp, by rw [h1, wordMat_nil, mul_one]⟩
  | cons j w ih =>
    obtain ⟨a, ha, u, hu, hw⟩ := ih
    obtain ⟨b, hb, v, hv, hj⟩ := hrw j a ha
    refine ⟨b, hb, v ++ u, ?_, ?_⟩
    · intro i hi
      rcases List.mem_append.mp hi with hi | hi
      · exact hv i hi
      · exact hu i hi
    · rw [wordMat_cons, hw, ← mul_assoc, hj, wordMat_append, mul_assoc]

/-- **Coset disjointness.** -/
theorem checkCosetCert_disjoint {R : RootDatum n} {c : RawCosetCert n}
    (h : checkCosetCert R c = true) {a b : ℕ} (ha : a < c.reps.length) (hb : b < c.reps.length)
    {u v : Word n} (hu : ∀ i ∈ u, i ∈ c.hgens) (hv : ∀ i ∈ v, i ∈ c.hgens)
    (heq : wordMat R (c.rep a) * wordMat R u = wordMat R (c.rep b) * wordMat R v) : a = b := by
  obtain ⟨-, -, hfix, hdist⟩ := checkCosetCert_spec h
  have himg : wordMat R (c.rep a) *ᵥ toVec n c.lam = wordMat R (c.rep b) *ᵥ toVec n c.lam := by
    calc wordMat R (c.rep a) *ᵥ toVec n c.lam
        = wordMat R (c.rep a) *ᵥ (wordMat R u *ᵥ toVec n c.lam) := by
          rw [wordMat_fix_of_hgens hfix u hu]
      _ = (wordMat R (c.rep b) * wordMat R v) *ᵥ toVec n c.lam := by rw [mulVec_mulVec, heq]
      _ = wordMat R (c.rep b) *ᵥ (wordMat R v *ᵥ toVec n c.lam) := (mulVec_mulVec _ _ _).symm
      _ = wordMat R (c.rep b) *ᵥ toVec n c.lam := by rw [wordMat_fix_of_hgens hfix v hv]
  rcases lt_trichotomy a b with hab | rfl | hab
  · exact absurd himg (hdist a b hab hb)
  · rfl
  · exact absurd himg.symm (hdist b a hab ha)

/-! ### Closure certificates for the subgroup `H` -/

/-- Closure of `L` under right multiplication by the `H` generators, with the identity. -/
def checkSubClosure (R : RootDatum n) (gens : List (Fin n)) (L : List (Word n)) : Bool :=
  let mats := L.map (lword R)
  lmem n (lone n) mats &&
  mats.all (fun x => gens.all fun i => lmem n (lmul n x (lrefl R i)) mats)

theorem checkSubClosure_complete {R : RootDatum n} {gens : List (Fin n)} {L : List (Word n)}
    (h : checkSubClosure R gens L = true) (u : Word n) (hu : ∀ i ∈ u, i ∈ gens) :
    ∃ v ∈ L, wordMat R v = wordMat R u := by
  simp only [checkSubClosure, Bool.and_eq_true, List.all_eq_true, List.mem_map,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at h
  obtain ⟨h1, h2⟩ := h
  induction u using List.reverseRecOn with
  | nil =>
    obtain ⟨y, hy, hy1⟩ := (lmem_iff _ _).mp h1
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hy
    exact ⟨v, hv, by rw [← toMat_lword, hy1, toMat_lone, wordMat_nil]⟩
  | append_singleton u i ih =>
    obtain ⟨v, hv, hvu⟩ := ih fun k hk => hu k (List.mem_append_left _ hk)
    obtain ⟨y, hy, hyx⟩ := (lmem_iff _ _).mp (h2 v hv i (hu i (by simp)))
    obtain ⟨v', hv', rfl⟩ := List.mem_map.mp hy
    refine ⟨v', hv', ?_⟩
    rw [← toMat_lword, hyx, toMat_lmul, toMat_lword, toMat_lrefl, hvu, wordMat_append,
      wordMat_singleton]

/-! ### Shards and assembly -/

/-- Order shard for coset `a`: every `r_a h`, `h ∈ L`, satisfies `x ^ m = 1` for a claimed maximum. -/
def checkShard (R : RootDatum n) (c : RawCosetCert n) (L : List (Word n)) (maxima : List ℕ)
    (a : ℕ) : Bool :=
  let r := lword R (c.rep a)
  L.all fun v => maxima.any fun m => lisOne n (lpow n (lmul n r (lword R v)) m)

/-- A coset bundle: coset certificate, closure certificate for `H`, claimed maxima, witnesses. -/
structure CosetBundle (n : ℕ) where
  datum : RootDatum n
  coset : RawCosetCert n
  subgroup : List (Word n)
  maxima : List ℕ
  witnesses : List (RawOrderCert n)

/-- **Assembly**: the shard list is complete (one shard per representative index). -/
def checkCosetBundle (b : CosetBundle n) : Bool :=
  checkCosetCert b.datum b.coset &&
  checkSubClosure b.datum b.coset.hgens b.subgroup &&
  (List.range b.coset.reps.length).all (checkShard b.datum b.coset b.subgroup b.maxima) &&
  b.maxima.all (fun m => decide (0 < m)) &&
  b.witnesses.all (checkOrderCert b.datum) &&
  b.maxima.all (fun m => b.witnesses.any fun c => c.order.val == m)

/-- **Soundness of the sharded coset route**: exact spectrum, no stabilizer theorem needed. -/
theorem checkCosetBundle_sound (b : CosetBundle n) (h : checkCosetBundle b = true) :
    omega b.datum = divClosure {m | m ∈ b.maxima} := by
  simp only [checkCosetBundle, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq, List.any_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hc, hsub⟩, hsh⟩, hpos⟩, hwit⟩, hcov⟩ := h
  apply Set.Subset.antisymm
  · intro d hd
    obtain ⟨w, rfl⟩ := (mem_omega_iff _ d).mp hd
    obtain ⟨a, ha, u, hu, hw⟩ := checkCosetCert_cover hc w
    obtain ⟨v, hv, hvu⟩ := checkSubClosure_complete hsub u hu
    have := hsh a ha
    simp only [checkShard, List.all_eq_true, List.any_eq_true] at this
    obtain ⟨m, hm, h1⟩ := this v hv
    rw [lisOne_iff, toMat_lpow, toMat_lmul, toMat_lword, toMat_lword, hvu, ← hw] at h1
    exact ⟨m, hm, orderOf_dvd_of_pow_eq_one h1⟩
  · rintro d ⟨m, hm, hdm⟩
    obtain ⟨c, hc', rfl⟩ := hcov m hm
    exact omega_dvd_closed _ (mem_omega_of_checkOrderCert (hwit c hc')) (hpos _ hm) hdm

/-! ### Pilot: `W(A₃)` as 4 cosets of `W(A₂) = ⟨s₀, s₁⟩` -/

/-- Coset certificate with `λ = (1, 2, 3)` (fixed by `s₀`, `s₁`). -/
def cosetA3 : RawCosetCert 3 where
  reps := [[], [2], [1, 2], [0, 1, 2]]
  hgens := [0, 1]
  lam := [1, 2, 3]
  rewrites := [(0, 0, 0, [0]), (0, 1, 1, [0]), (0, 2, 3, []), (0, 3, 2, []), (1, 0, 0, [1]),
    (1, 1, 2, []), (1, 2, 1, []), (1, 3, 3, [0]), (2, 0, 1, []), (2, 1, 0, []), (2, 2, 2, [1]),
    (2, 3, 3, [1])]

theorem cosetA3_ok : checkCosetCert rdA3 cosetA3 = true := by decide +kernel

/-- Negative test: one wrong rewriting identity is rejected. -/
theorem cosetA3_wrong_rewrite_fails :
    checkCosetCert rdA3 { cosetA3 with rewrites := (0, 0, 0, []) :: cosetA3.rewrites.tail } =
      false := by
  decide +kernel

/-- Negative test: two representatives with equal images of `λ` are rejected. -/
theorem cosetA3_equal_images_fails :
    checkCosetCert rdA3 { cosetA3 with reps := [[], [2], [1, 2], [0]] } = false := by
  decide +kernel

/-- The sharded `W(A₃)` bundle. -/
def cosetBundleA3 : CosetBundle 3 where
  datum := rdA3
  coset := cosetA3
  subgroup := [[], [0], [1], [0, 1], [1, 0], [0, 1, 0]]
  maxima := [3, 4]
  witnesses := [⟨[0, 1], ⟨[(3, 1)], 3⟩⟩, ⟨[0, 1, 2], ⟨[(2, 2)], 4⟩⟩]

theorem cosetBundleA3_ok : checkCosetBundle cosetBundleA3 = true := by decide +kernel

/-- `ω(W(A₃))` re-derived through the coset route (agrees with `omega_A3`). -/
theorem omega_A3_via_cosets : omega rdA3 = divClosure {m | m ∈ [3, 4]} := by
  have h := checkCosetBundle_sound _ cosetBundleA3_ok
  rwa [show cosetBundleA3.datum = rdA3 from rfl,
    show cosetBundleA3.maxima = [3, 4] from rfl] at h

/-! ### `E₈` transversal vector (RFC rev. 2 §6.2) -/

/-- `λ = C⁻¹ e₇` for the Mathlib `E₈` Cartan matrix is integral: `C λ = e₇`. -/
theorem E8_lambda : rdE8.cartan *ᵥ ![2, 3, 4, 6, 5, 4, 3, 2] = Pi.single 7 1 := by
  decide +kernel

/-- `λ` is fixed by the `H = ⟨s₀, …, s₆⟩` generators. -/
theorem E8_lambda_fixed (g : Fin 8) (hg : g.val < 7) :
    refl rdE8 g *ᵥ ![2, 3, 4, 6, 5, 4, 3, 2] = ![2, 3, 4, 6, 5, 4, 3, 2] := by
  ext k
  rw [refl_mulVec]
  split_ifs with hk
  · have h := congrFun E8_lambda g
    simp only [mulVec, dotProduct] at h
    rw [h, Pi.single_apply, if_neg (by intro h7; rw [h7] at hg; simp at hg), sub_zero]
  · rfl

end SpectrumVM

end
