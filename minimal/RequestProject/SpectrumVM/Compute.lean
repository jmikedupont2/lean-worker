module

public import RequestProject.SpectrumVM.Conventions
public import RequestProject.SpectrumVM.Order

/-!
# SpectrumVM §5/§7: the kernel bridge for the matrix backend

Kernel-reducible list matrices with a proved bridge `toMat` to Mathlib matrices.  A `Bool`
checker `checkOrderCert` replays an order certificate (K1 + K2) by exact integer matrix powering;
its soundness theorem `checkOrderCert_sound` turns a kernel evaluation `checkOrderCert R c = true`
(by `decide`, no `native_decide`) into the statement `orderOf (wordMat R c.word) = c.order.val`.
This is the "checker soundness + concrete kernel proof of `h`" shape required by review §1.
-/

@[expose] public section

namespace SpectrumVM

open Matrix

variable {n : ℕ}

/-- List-of-rows integer matrix (wire / kernel format). -/
abbrev LMat := List (List ℤ)

/-- Entry lookup, defaulting to `0` outside the stored range. -/
def lget (A : LMat) (i j : ℕ) : ℤ := (A.getD i []).getD j 0

/-- Bridge to Mathlib matrices. -/
def toMat (n : ℕ) (A : LMat) : Matrix (Fin n) (Fin n) ℤ := fun i j => lget A i j

/-- Tabulate an `n × n` list matrix from an entry function. -/
def ltab (n : ℕ) (f : ℕ → ℕ → ℤ) : LMat :=
  (List.range n).map fun i => (List.range n).map fun j => f i j

theorem lget_ltab {f : ℕ → ℕ → ℤ} {i j : ℕ} (hi : i < n) (hj : j < n) :
    lget (ltab n f) i j = f i j := by
  simp [lget, ltab, List.getD_eq_getElem?_getD, hi, hj]

theorem toMat_ltab (f : ℕ → ℕ → ℤ) (i j : Fin n) : toMat n (ltab n f) i j = f i j := by
  simp [toMat, lget_ltab i.isLt j.isLt]

def lmul (n : ℕ) (A B : LMat) : LMat :=
  ltab n fun i j => ((List.range n).map fun k => lget A i k * lget B k j).sum

def lone (n : ℕ) : LMat := ltab n fun i j => if i = j then 1 else 0

def lpow (n : ℕ) (A : LMat) : ℕ → LMat
  | 0 => lone n
  | k + 1 => lmul n (lpow n A k) A

/-- Exact identity test on the `n × n` block. -/
def lisOne (n : ℕ) (A : LMat) : Bool :=
  (List.range n).all fun i => (List.range n).all fun j => lget A i j == if i = j then 1 else 0

theorem toMat_lmul (A B : LMat) : toMat n (lmul n A B) = toMat n A * toMat n B := by
  ext i j
  rw [lmul, toMat_ltab, mul_apply]
  simp only [toMat]
  rw [Fin.sum_univ_eq_sum_range (fun k => lget A i k * lget B k j) n]
  rfl

theorem toMat_lone : toMat n (lone n) = 1 := by
  ext i j
  rw [lone, toMat_ltab, one_apply]
  simp [Fin.ext_iff]

theorem toMat_lpow (A : LMat) (k : ℕ) : toMat n (lpow n A k) = toMat n A ^ k := by
  induction k with
  | zero => simp [lpow, toMat_lone]
  | succ k ih => rw [lpow, toMat_lmul, ih, pow_succ]

theorem lisOne_iff (A : LMat) : lisOne n A = true ↔ toMat n A = 1 := by
  simp only [lisOne, List.all_eq_true, List.mem_range, beq_iff_eq]
  constructor
  · intro h; ext i j
    simp only [toMat]
    rw [h i i.isLt j j.isLt, one_apply]; simp [Fin.ext_iff]
  · intro h i hi j hj
    have := congrFun (congrFun h ⟨i, hi⟩) ⟨j, hj⟩
    simpa [toMat, one_apply, Fin.ext_iff] using this

/-- Cartan entries indexed by naturals (zero outside range). -/
def cartN (R : RootDatum n) (a b : ℕ) : ℤ :=
  if h : a < n ∧ b < n then R.cartan ⟨a, h.1⟩ ⟨b, h.2⟩ else 0

/-- List form of the simple reflection `s_i`. -/
def lrefl (R : RootDatum n) (i : Fin n) : LMat :=
  ltab n fun j k => (if j = k then 1 else 0) - (if j = i.val then cartN R i.val k else 0)

theorem toMat_lrefl (R : RootDatum n) (i : Fin n) : toMat n (lrefl R i) = refl R i := by
  ext j k
  rw [lrefl, toMat_ltab]
  simp [refl, cartN, Fin.ext_iff]

/-- List form of a word. -/
def lword (R : RootDatum n) (w : Word n) : LMat :=
  w.foldr (fun i acc => lmul n (lrefl R i) acc) (lone n)

theorem toMat_lword (R : RootDatum n) (w : Word n) : toMat n (lword R w) = wordMat R w := by
  induction w with
  | nil => simp [lword, toMat_lone]
  | cons i w ih =>
    simp only [lword, List.foldr_cons] at ih ⊢
    rw [toMat_lmul, ih, toMat_lrefl, wordMat_cons]

/-- Raw order certificate (RFC §4): a word and a claimed factored order. -/
structure RawOrderCert (n : ℕ) where
  word : Word n
  order : RawFactoredOrder
  deriving Repr

/-- Order check from an already evaluated matrix. -/
def checkOrderMat (n : ℕ) (M : LMat) (f : RawFactoredOrder) : Bool :=
  checkFactorization f && lisOne n (lpow n M f.val) &&
    f.fac.all fun pe => !lisOne n (lpow n M (f.val / pe.1))

/-- **ORDER.CHECK** (RFC §8): replay of an order certificate by exact matrix powering. -/
def checkOrderCert (R : RootDatum n) (c : RawOrderCert n) : Bool :=
  checkOrderMat n (lword R c.word) c.order

theorem checkOrderMat_sound {M : LMat} {f : RawFactoredOrder} (h : checkOrderMat n M f = true) :
    orderOf (toMat n M) = f.val := by
  simp only [checkOrderMat, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true] at h
  obtain ⟨⟨hf, h1⟩, h2⟩ := h
  refine orderOf_eq_of_factored f hf ?_ fun pe hpe => ?_
  · rw [← toMat_lpow, ← lisOne_iff]; exact h1
  · rw [← toMat_lpow, Ne, ← lisOne_iff, h2 pe hpe]; simp

/-- **Order certificate soundness** (K1 + K2 + K3 combined). -/
theorem checkOrderCert_sound {R : RootDatum n} {c : RawOrderCert n}
    (h : checkOrderCert R c = true) : orderOf (wordMat R c.word) = c.order.val := by
  rw [← toMat_lword]; exact checkOrderMat_sound h

/-- Validated order certificate (proof-carrying, review §6). -/
structure ValidOrderCert (R : RootDatum n) extends RawOrderCert n where
  valid : checkOrderCert R toRawOrderCert = true

theorem ValidOrderCert.orderOf_eq {R : RootDatum n} (c : ValidOrderCert R) :
    orderOf (wordMat R c.word) = c.order.val := checkOrderCert_sound c.valid

end SpectrumVM

end
