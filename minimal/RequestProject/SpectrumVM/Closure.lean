module

public import RequestProject.SpectrumVM.Spectrum
public import RequestProject.SpectrumVM.OrderIdeal

/-!
# SpectrumVM §6: completeness certificates

* **C1** (`closure_eq_of_closed`): abstract closure certificate theorem.
* **Coset rewriting certificate** (review §4, `coset_cover`, `coset_disjoint`): the computational
  transversal route for large groups, independent of any stabilizer theorem.
* A concrete `Bool` replay `checkClosureCert` for closure certificates whose elements are given as
  words, with soundness theorems giving `Nat.card (MatrixW R) = L.length` (|L| = |W| is a
  consequence, not an assumption) and the exact spectrum `omega R = divClosure maxima`.
-/

@[expose] public section

namespace SpectrumVM

open Matrix

variable {n : ℕ}

/-! ### C1, abstract form -/

/-- **C1.** A set containing `1` and closed under right multiplication by every generator contains
the submonoid generated; if moreover every element has a generation path, they are equal. -/
theorem closure_subset_of_closed {M : Type*} [Monoid M] (S L : Set M) (h1 : (1 : M) ∈ L)
    (hmul : ∀ x ∈ L, ∀ s ∈ S, x * s ∈ L) : (Submonoid.closure S : Set M) ⊆ L := by
  intro g hg
  induction hg using Submonoid.closure_induction_right with
  | one => exact h1
  | mul_right x _ s hs ih => exact hmul x ih s hs

theorem closure_eq_of_closed {M : Type*} [Monoid M] (S L : Set M) (h1 : (1 : M) ∈ L)
    (hmul : ∀ x ∈ L, ∀ s ∈ S, x * s ∈ L) (hgen : L ⊆ Submonoid.closure S) :
    (Submonoid.closure S : Set M) = L :=
  Set.Subset.antisymm (closure_subset_of_closed S L h1 hmul) hgen

/-! ### Coset rewriting certificate (review §4) -/

/-- Rewriting `s_j r_a = r_b h_{j,a}` with `h_{j,a} ∈ H` and a representative equal to `1` show
that `⋃_a r_a H` covers the generated monoid. -/
theorem coset_cover {G ι κ : Type*} [Monoid G] (s : ι → G) (H : Submonoid G) (r : κ → G)
    (a₀ : κ) (hr₀ : r a₀ = 1) (hrw : ∀ j a, ∃ b, ∃ h ∈ H, s j * r a = r b * h) :
    ∀ g ∈ Submonoid.closure (Set.range s), ∃ a, ∃ h ∈ H, g = r a * h := by
  intro g hg
  induction hg using Submonoid.closure_induction_left with
  | one => exact ⟨a₀, 1, H.one_mem, by rw [hr₀, one_mul]⟩
  | mul_left x hx y _ ih =>
    obtain ⟨j, rfl⟩ := hx
    obtain ⟨a, h, hh, rfl⟩ := ih
    obtain ⟨b, h', hh', hb⟩ := hrw j a
    exact ⟨b, h' * h, H.mul_mem hh' hh, by rw [← mul_assoc, hb, mul_assoc]⟩

/-- Distinct images of a vector fixed by `H` prove the cosets `r_a H` are pairwise disjoint. -/
theorem coset_disjoint {G V κ : Type*} [Monoid G] (act : G → V → V)
    (hact : ∀ g h v, act (g * h) v = act g (act h v)) (H : Submonoid G) (v : V)
    (hfix : ∀ h ∈ H, act h v = v) (r : κ → G) (hinj : Function.Injective fun a => act (r a) v)
    {a b : κ} {h h' : G} (hh : h ∈ H) (hh' : h' ∈ H) (heq : r a * h = r b * h') : a = b := by
  apply hinj
  show act (r a) v = act (r b) v
  calc act (r a) v = act (r a) (act h v) := by rw [hfix h hh]
    _ = act (r a * h) v := (hact _ _ _).symm
    _ = act (r b * h') v := by rw [heq]
    _ = act (r b) (act h' v) := hact _ _ _
    _ = act (r b) v := by rw [hfix h' hh']

/-! ### Concrete closure certificates over list matrices -/

/-- Exact entrywise equality test on the `n × n` block. -/
def lisEq (n : ℕ) (A B : LMat) : Bool :=
  (List.range n).all fun i => (List.range n).all fun j => lget A i j == lget B i j

theorem lisEq_iff (A B : LMat) : lisEq n A B = true ↔ toMat n A = toMat n B := by
  simp only [lisEq, List.all_eq_true, List.mem_range, beq_iff_eq]
  constructor
  · intro h; ext i j; exact h i i.isLt j j.isLt
  · intro h i hi j hj
    exact congrFun (congrFun h ⟨i, hi⟩) ⟨j, hj⟩

/-- Membership by exact matrix equality. -/
def lmem (n : ℕ) (x : LMat) (L : List LMat) : Bool := L.any (lisEq n x)

theorem lmem_iff (x : LMat) (L : List LMat) :
    lmem n x L = true ↔ ∃ y ∈ L, toMat n y = toMat n x := by
  simp only [lmem, List.any_eq_true, lisEq_iff]
  exact ⟨fun ⟨y, hy, h⟩ => ⟨y, hy, h.symm⟩, fun ⟨y, hy, h⟩ => ⟨y, hy, h.symm⟩⟩

/-- Pairwise distinctness by exact matrix equality (RFC §6.1 condition 4). -/
def lpairwiseDistinct (n : ℕ) : List LMat → Bool
  | [] => true
  | x :: t => !(lmem n x t) && lpairwiseDistinct n t

theorem lpairwiseDistinct_sound {L : List LMat} (h : lpairwiseDistinct n L = true) :
    (L.map (toMat n)).Nodup := by
  induction L with
  | nil => simp
  | cons x t ih =>
    simp only [lpairwiseDistinct, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
    refine List.nodup_cons.mpr ⟨?_, ih h.2⟩
    intro hx
    obtain ⟨y, hy, hyx⟩ := List.mem_map.mp hx
    have : lmem n x t = true := (lmem_iff x t).mpr ⟨y, hy, hyx⟩
    rw [h.1] at this; exact absurd this (by decide)

/-- **ENUM.CLOSE replay** (RFC §6.1).  Elements are given as words (so each has a generation path
by construction).  The checker verifies: the identity occurs; right multiplication by every
generator stays in the list (exact matrix equality); elements are pairwise distinct; and every
element `x` satisfies `x ^ m = 1` for some claimed maximal order `m`. -/
def checkClosureCert (R : RootDatum n) (L : List (Word n)) (maxima : List ℕ) : Bool :=
  let mats := L.map (lword R)
  lmem n (lone n) mats &&
  mats.all (fun x => (List.finRange n).all fun i => lmem n (lmul n x (lrefl R i)) mats) &&
  lpairwiseDistinct n mats &&
  mats.all (fun x => maxima.any fun m => lisOne n (lpow n x m))

theorem checkClosureCert_spec {R : RootDatum n} {L : List (Word n)} {maxima : List ℕ}
    (h : checkClosureCert R L maxima = true) :
    (∃ v ∈ L, wordMat R v = 1) ∧
    (∀ v ∈ L, ∀ i : Fin n, ∃ u ∈ L, wordMat R u = wordMat R v * refl R i) ∧
    (L.map (wordMat R)).Nodup ∧
    (∀ v ∈ L, ∃ m ∈ maxima, wordMat R v ^ m = 1) := by
  simp only [checkClosureCert, Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
    List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨y, hy, hy1⟩ := (lmem_iff _ _).mp h1
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hy
    exact ⟨v, hv, by rw [← toMat_lword, hy1, toMat_lone]⟩
  · intro v hv i
    obtain ⟨y, hy, hyx⟩ := (lmem_iff _ _).mp (h2 v hv i (List.mem_finRange i))
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hy
    exact ⟨u, hu, by rw [← toMat_lword, hyx, toMat_lmul, toMat_lword, toMat_lrefl]⟩
  · have := lpairwiseDistinct_sound h3
    rwa [List.map_map, show toMat n ∘ lword R = wordMat R from funext (toMat_lword R)] at this
  · intro v hv
    obtain ⟨m, hm, hm1⟩ := h4 v hv
    exact ⟨m, hm, by rw [← toMat_lword, ← toMat_lpow, ← lisOne_iff]; exact hm1⟩

/-- Every word matrix occurs in a replayed closure certificate (C1 applied to `MatrixW`). -/
theorem checkClosureCert_complete {R : RootDatum n} {L : List (Word n)} {maxima : List ℕ}
    (h : checkClosureCert R L maxima = true) (w : Word n) : ∃ v ∈ L, wordMat R v = wordMat R w := by
  obtain ⟨⟨v₀, hv₀, h1⟩, hcl, -, -⟩ := checkClosureCert_spec h
  induction w using List.reverseRecOn with
  | nil => exact ⟨v₀, hv₀, by rw [h1, wordMat_nil]⟩
  | append_singleton w i ih =>
    obtain ⟨v, hv, hvw⟩ := ih
    obtain ⟨u, hu, hu'⟩ := hcl v hv i
    exact ⟨u, hu, by rw [hu', hvw, wordMat_append, wordMat_singleton]⟩

/-- **C1 consequence.** A replayed closure certificate determines the group order exactly:
`|MatrixW R| = |L|`. -/
theorem card_MatrixW_of_closureCert {R : RootDatum n} {L : List (Word n)} {maxima : List ℕ}
    (h : checkClosureCert R L maxima = true) : Nat.card (MatrixW R) = L.length := by
  obtain ⟨-, -, hnd, -⟩ := checkClosureCert_spec h
  have hnd' : (L.map (wordUnit R)).Nodup := by
    refine List.Nodup.of_map Units.val ?_
    rw [List.map_map]
    convert hnd using 2
    exact funext (coe_wordUnit R)
  have hset : ((MatrixW R : Set (Matrix (Fin n) (Fin n) ℤ)ˣ)) =
      ((L.map (wordUnit R)).toFinset : Set _) := by
    ext g
    simp only [SetLike.mem_coe, List.coe_toFinset, Set.mem_setOf_eq, List.mem_map]
    rw [mem_MatrixW_iff]
    constructor
    · rintro ⟨w, hw⟩
      obtain ⟨v, hv, hvw⟩ := checkClosureCert_complete h w
      exact ⟨v, hv, Units.ext (by rw [coe_wordUnit, hvw, hw])⟩
    · rintro ⟨v, -, rfl⟩
      exact ⟨v, coe_wordUnit R v⟩
  rw [← SetLike.coe_sort_coe, hset, Nat.card_coe_set_eq, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup hnd', List.length_map]

/-- **Verified spectrum from a closure certificate.** If the closure certificate replays and every
claimed maximal order is positive and witnessed, then the spectrum is exactly the divisor closure
of the claimed maxima. -/
theorem omega_eq_of_closureCert {R : RootDatum n} {L : List (Word n)} {maxima : List ℕ}
    (h : checkClosureCert R L maxima = true) (hpos : ∀ m ∈ maxima, 0 < m)
    (hwit : ∀ m ∈ maxima, m ∈ omega R) : omega R = divClosure {m | m ∈ maxima} := by
  obtain ⟨-, -, -, hord⟩ := checkClosureCert_spec h
  apply Set.Subset.antisymm
  · intro d hd
    obtain ⟨w, rfl⟩ := (mem_omega_iff R d).mp hd
    obtain ⟨v, hv, hvw⟩ := checkClosureCert_complete h w
    obtain ⟨m, hm, hm1⟩ := hord v hv
    exact ⟨m, hm, by rw [← hvw]; exact orderOf_dvd_of_pow_eq_one hm1⟩
  · rintro d ⟨m, hm, hdm⟩
    exact omega_dvd_closed R (hwit m hm) (hpos m hm) hdm

/-- Lower bound from witnesses: the divisors of witnessed positive orders lie in the spectrum. -/
theorem divisorsOf_subset_omega (R : RootDatum n) {l : List ℕ} (hpos : ∀ m ∈ l, 0 < m)
    (hwit : ∀ m ∈ l, m ∈ omega R) : (divisorsOf l : Set ℕ) ⊆ omega R := by
  rw [← divClosure_eq_divisorsOf l hpos]
  rintro d ⟨m, hm, hdm⟩
  exact omega_dvd_closed R (hwit m hm) (hpos m hm) hdm

end SpectrumVM

end
