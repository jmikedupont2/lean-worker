module

public import RequestProject.SpectrumVM.SmallTypes

/-!
# SpectrumVM: assurance levels, proposition-linked claims, and the bundle contract

This file pins down the contract between the fast checker and the Lean kernel (review §1 and the
follow-up request that `BundleCorrect` be defined precisely).

* `Assurance` distinguishes *external execution*, *sound-checker execution* and
  *kernel-established* results.
* `VerificationClaim` links a proposition digest, a certificate digest and a verifier digest; a
  digest identifies bytes and is never evidence by itself.
* `Evidence P` attaches a claim to the proposition `P`.  Only the `kernel` constructor reports
  `kernelEstablished`, and it carries a proof of `P` (`Evidence.sound`): no assurance level is
  reachable without supporting evidence.
* `Bundle` (raw wire format), the `Bool` checker `checkBundle`, the proposition `BundleCorrect`, and
  `checkBundle_sound : checkBundle b = true → BundleCorrect b`.  A *kernel-established* bundle is a
  closed Lean proof of `checkBundle b = true` (here by `decide +kernel`), as for `bundleA4`.
-/

@[expose] public section

namespace SpectrumVM

/-- Assurance levels (RFC rev. 2 §3.1). -/
inductive Assurance
  /-- Witnessed orders only; completeness not claimed. -/
  | observed
  /-- An imported claim or a named unproved hypothesis. -/
  | external
  /-- A fast program reports that its completeness checks passed. -/
  | externalExecution
  /-- The algorithm has a Lean soundness theorem, but this execution was not replayed in the
  kernel. -/
  | soundCheckerExecution
  /-- Lean has a closed proof of the concrete proposition. -/
  | kernelEstablished
  deriving DecidableEq, Repr

/-- Proposition-linked verification claim: which proposition, which certificate bytes, which
verifier (the named verification authority).  Metadata only. -/
structure VerificationClaim where
  propositionDigest : String
  certificateDigest : String
  verifierDigest : String
  deriving DecidableEq, Repr

/-- Evidence for a proposition `P`, with its assurance level.  Only `kernel` carries a proof. -/
inductive Evidence (P : Prop) : Type
  | observed
  | external (source : String) (hypothesis : String)
  | externalExecution (claim : VerificationClaim)
  | soundChecker (claim : VerificationClaim)
  | kernel (proof : P) (claim : VerificationClaim)

def Evidence.assurance {P : Prop} : Evidence P → Assurance
  | .observed => .observed
  | .external _ _ => .external
  | .externalExecution _ => .externalExecution
  | .soundChecker _ => .soundCheckerExecution
  | .kernel _ _ => .kernelEstablished

/-- A `kernelEstablished` label is backed by a proof: no assurance without evidence. -/
theorem Evidence.sound {P : Prop} (e : Evidence P) (h : e.assurance = .kernelEstablished) : P := by
  cases e with
  | kernel p _ => exact p
  | _ => simp [Evidence.assurance] at h

/-- Assurance test (RFC §12): an external execution report is never displayed as
kernel-established. -/
example (P : Prop) (c : VerificationClaim) :
    (Evidence.externalExecution c : Evidence P).assurance ≠ .kernelEstablished := by
  simp [Evidence.assurance]

/-- Assurance test: evidence for `False` can never be kernel-established. -/
example (e : Evidence False) : e.assurance ≠ .kernelEstablished := fun h => e.sound h

/-- Raw completeness bundle: a root datum, a closure certificate (all elements as words), claimed
maximal orders, and one order certificate per claimed maximum. -/
structure Bundle (n : ℕ) where
  datum : RootDatum n
  closure : List (Word n)
  maxima : List ℕ
  witnesses : List (RawOrderCert n)

/-- **The concrete spectrum proposition** certified by a bundle: the group order of `MatrixW` is
the length of the closure list, and the spectrum is exactly the divisor closure of the claimed
maxima. -/
def BundleCorrect {n : ℕ} (b : Bundle n) : Prop :=
  Nat.card (MatrixW b.datum) = b.closure.length ∧
    omega b.datum = divClosure {m | m ∈ b.maxima}

/-- The bundle checker. -/
def checkBundle {n : ℕ} (b : Bundle n) : Bool :=
  checkClosureCert b.datum b.closure b.maxima &&
  b.maxima.all (fun m => decide (0 < m)) &&
  b.witnesses.all (checkOrderCert b.datum) &&
  b.maxima.all (fun m => b.witnesses.any fun c => c.order.val == m)

/-- **Checker soundness.** -/
theorem checkBundle_sound {n : ℕ} (b : Bundle n) (h : checkBundle b = true) : BundleCorrect b := by
  simp only [checkBundle, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    List.any_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hcl, hpos⟩, hwit⟩, hcov⟩ := h
  refine ⟨card_MatrixW_of_closureCert hcl, omega_eq_of_closureCert hcl hpos fun m hm => ?_⟩
  obtain ⟨c, hc, rfl⟩ := hcov m hm
  exact mem_omega_of_checkOrderCert (hwit c hc)

/-- Kernel-established evidence from a closed proof of `checkBundle b = true`. -/
def Bundle.kernelEvidence {n : ℕ} (b : Bundle n) (h : checkBundle b = true)
    (claim : VerificationClaim) : Evidence (BundleCorrect b) :=
  .kernel (checkBundle_sound b h) claim

/-- The `W(A₄)` pilot bundle. -/
def bundleA4 : Bundle 4 where
  datum := rdA4
  closure := closureA4
  maxima := [4, 5, 6]
  witnesses := [⟨[0, 1, 2], ⟨[(2, 2)], 4⟩⟩, ⟨[0, 1, 2, 3], ⟨[(5, 1)], 5⟩⟩,
    ⟨[0, 1, 3], ⟨[(2, 1), (3, 1)], 6⟩⟩]

set_option maxRecDepth 100000 in
theorem checkBundle_A4 : checkBundle bundleA4 = true := by decide +kernel

/-- `BundleCorrect bundleA4`, kernel-established. -/
theorem bundleA4_correct : BundleCorrect bundleA4 := checkBundle_sound _ checkBundle_A4

end SpectrumVM

end
