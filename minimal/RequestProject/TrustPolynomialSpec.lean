import RequestProject.TrustPolynomial

/-!
# What the trust polynomial and the lattice validator actually check

Proved facts about `TrustCapsule.evaluatePolynomial` and `TrustCapsule.validateLatticeBounds`
(`RequestProject/TrustPolynomial.lean`). Together they pin down what the validator means:

* `validateLatticeBounds_eq_true_iff`: the verdict is the strict two-sided comparison
  `N < P(C,K,B,D) < M`, where `N` and `M` are the `orderExponent` fields.
* `evaluatePolynomial_eq`: `P = C + 10·K + ⌊B / 1024⌋ + 100·D`. It is linear in `C`, `K`, `D`
  and floor-linear in `B`.
* `evaluatePolynomial_mono`: `P` is monotone in each variable.
* `evaluatePolynomial_surjective`: every natural number is a weight.
* `exists_valid_iff`: for fixed bounds, some capsule passes iff `N + 1 < M`.
* `validateLatticeBounds_indep_characteristic`: the `characteristic` fields are never read.
* `validateLatticeBounds_indep_constants_axioms`: neither are the `constants` and `axioms`
  lists.
* `evaluatePolynomial_binary_floor`: footprints that agree after dividing by 1024 get the same
  weight, so the validator cannot see changes under 1 KB.
* `validateLatticeBounds_bootstrap_floor`: a valid capsule must have `M > 100·D`.

`validateFieldOrderBounds` is an alternative reading that compares against the field orders
`p ^ n` instead of the exponents `n`. `lattice_vs_field_order` shows that the two readings
disagree on a concrete capsule.
-/

namespace TrustCapsule

/-- The validator returns `true` exactly when the weight lies strictly between the two
`orderExponent` fields. -/
theorem validateLatticeBounds_eq_true_iff (c : Capsule) :
    validateLatticeBounds c = true ↔
      c.lowerBound.orderExponent < evaluatePolynomial c.poly ∧
        evaluatePolynomial c.poly < c.upperBound.orderExponent := by
  simp [validateLatticeBounds]

/-- Closed form of the weight: `C + 10·K + ⌊B / 1024⌋ + 100·D`. -/
theorem evaluatePolynomial_eq (p : TrustPolynomial) :
    evaluatePolynomial p =
      p.logicalComplexity + 10 * p.kernelWeight + p.binaryFootprint / 1024 +
        100 * p.bootstrapDepth := by
  simp only [evaluatePolynomial]
  omega

/-- The weight is monotone: raising any of `C`, `K`, `B`, `D` never lowers it. -/
theorem evaluatePolynomial_mono {p q : TrustPolynomial}
    (hC : p.logicalComplexity ≤ q.logicalComplexity) (hK : p.kernelWeight ≤ q.kernelWeight)
    (hB : p.binaryFootprint ≤ q.binaryFootprint) (hD : p.bootstrapDepth ≤ q.bootstrapDepth) :
    evaluatePolynomial p ≤ evaluatePolynomial q := by
  have := Nat.div_le_div_right (c := 1024) hB
  rw [evaluatePolynomial_eq, evaluatePolynomial_eq]
  omega

/-- Every natural number is the weight of some polynomial (take `C = n`, the rest `0`). -/
theorem evaluatePolynomial_surjective (n : Nat) :
    ∃ p : TrustPolynomial, evaluatePolynomial p = n :=
  ⟨⟨n, 0, 0, 0⟩, by simp [evaluatePolynomial]⟩

/-- For fixed bounds, some capsule passes the validator iff the open window `(N, M)` contains a
natural number, i.e. `N + 1 < M`. The name, constants and axioms are arbitrary. -/
theorem exists_valid_iff (lo hi : FieldBound) (d : Lean.Name) (cs axs : List Lean.Name) :
    (∃ p : TrustPolynomial, validateLatticeBounds ⟨d, cs, axs, p, lo, hi⟩ = true) ↔
      lo.orderExponent + 1 < hi.orderExponent := by
  constructor
  · rintro ⟨p, hp⟩
    rw [validateLatticeBounds_eq_true_iff] at hp
    dsimp only at hp
    omega
  · intro h
    obtain ⟨p, hp⟩ := evaluatePolynomial_surjective (lo.orderExponent + 1)
    refine ⟨p, ?_⟩
    rw [validateLatticeBounds_eq_true_iff]
    show lo.orderExponent < evaluatePolynomial p ∧ evaluatePolynomial p < hi.orderExponent
    omega

/-- The `characteristic` fields of both bounds are never read by the validator. -/
theorem validateLatticeBounds_indep_characteristic (c : Capsule) (p q : Nat) :
    validateLatticeBounds
        { c with lowerBound := { c.lowerBound with characteristic := p },
                 upperBound := { c.upperBound with characteristic := q } } =
      validateLatticeBounds c := rfl

/-- The `constants` and `axioms` lists are never read by the validator either: the verdict
depends only on `poly` and the two exponents. -/
theorem validateLatticeBounds_indep_constants_axioms (c : Capsule) (cs axs : List Lean.Name) :
    validateLatticeBounds { c with constants := cs, axioms := axs } =
      validateLatticeBounds c := rfl

/-- Two footprints with the same `⌊B / 1024⌋` give the same weight, so changes under 1 KB are
invisible to the validator. -/
theorem evaluatePolynomial_binary_floor (p : TrustPolynomial) (b : Nat)
    (h : b / 1024 = p.binaryFootprint / 1024) :
    evaluatePolynomial { p with binaryFootprint := b } = evaluatePolynomial p := by
  simp only [evaluatePolynomial, h]

/-- Concretely: `B = 0` and `B = 1023` bytes get the same weight. -/
example : evaluatePolynomial ⟨0, 0, 0, 0⟩ = evaluatePolynomial ⟨0, 0, 1023, 0⟩ := by decide

/-- The bootstrap term dominates: a valid capsule needs an upper exponent above `100·D`. -/
theorem validateLatticeBounds_bootstrap_floor (c : Capsule)
    (h : validateLatticeBounds c = true) :
    100 * c.poly.bootstrapDepth < c.upperBound.orderExponent := by
  rw [validateLatticeBounds_eq_true_iff, evaluatePolynomial_eq] at h
  omega

/-- An alternative reading of the window: compare against the field orders `p ^ n` of
`GF(p ^ n)`, not against the exponents `n`. This is *not* the user's validator. It is offered
for comparison only. -/
def validateFieldOrderBounds (c : Capsule) : Bool :=
  let weight := evaluatePolynomial c.poly
  c.lowerBound.characteristic ^ c.lowerBound.orderExponent < weight &&
    weight < c.upperBound.characteristic ^ c.upperBound.orderExponent

theorem validateFieldOrderBounds_eq_true_iff (c : Capsule) :
    validateFieldOrderBounds c = true ↔
      c.lowerBound.characteristic ^ c.lowerBound.orderExponent < evaluatePolynomial c.poly ∧
        evaluatePolynomial c.poly <
          c.upperBound.characteristic ^ c.upperBound.orderExponent := by
  simp [validateFieldOrderBounds]

/-- The two readings disagree: with bounds `GF(2^4)` and `GF(2^10)` and weight `100`, the
exponent reading rejects (`100 ≥ 10`), while the field-order reading accepts
(`16 < 100 < 1024`). -/
theorem lattice_vs_field_order :
    let c : Capsule := ⟨`demo, [], [], ⟨100, 0, 0, 0⟩, ⟨2, 4⟩, ⟨2, 10⟩⟩
    validateLatticeBounds c = false ∧ validateFieldOrderBounds c = true := by
  decide

end TrustCapsule
