import RequestProject.Dasein15VM.UI.Mask

/-!
# RFC-0002 §3: certified traces, VM objects and badges

* `checkVMTrace_complete`: the converse of `checkVMTrace_sound` (a correct trace always passes
  the checker), so `checkVMTrace S s₀ s tr = true ↔ VMCorrect S s₀ s tr`.
* `TraceEntry S`: a named trace with its `VMCorrect` proof and a `VerificationClaim`.  Its
  evidence is `kernel`, and its assurance is *derived* from the evidence (`TraceEntry.assurance`),
  never stored independently.
* `Badge P` (§3.4): a claim plus evidence whose assurance is `kernelEstablished`; `Badge.sound`
  extracts the proof of `P` (obligation **S1**, via `Evidence.sound`).
* `VMObject n` (§3.2): spec, observable, certified traces, a mask, the order set `omega` that
  the mask claims to describe, the **user-supplied** hypothesis `maskHolds : mask.Holds omega`,
  and provenance.
  - `mkVMObject` builds an object whose mask is the observed mask of its certified traces; then
    `omega` is the semantic order set `specOrders spec obs` and `maskHolds` is *proved*
    (`observedMask_holds`), and the kind is `witnessedSubset`.
  - `declareVMObject` builds an object with a declared mask; `maskHolds` must be supplied.
-/

namespace Dasein15VM.UI

open SpectrumVM

variable {n : ℕ}

/-! ### Completeness of the trace checker -/

theorem checkChain_complete (S : VMSpec n) :
    ∀ (l : List (VMState n)), (∀ i (h : i + 1 < l.length), step S l[i] = some l[i + 1]) →
      checkChain S l = true
  | [], _ => rfl
  | [_], _ => rfl
  | s :: t :: rest, h => by
    simp only [checkChain, Bool.and_eq_true]
    refine ⟨(checkStep_iff S s t).2 (h 0 (by simp)), checkChain_complete S (t :: rest) ?_⟩
    intro i hi
    exact h (i + 1) (by simp at hi ⊢; omega)

/-- **Checker completeness**: a correct trace passes `checkVMTrace`. -/
theorem checkVMTrace_complete {S : VMSpec n} {s₀ s : VMState n} {tr : List (VMState n)}
    (h : VMCorrect S s₀ s tr) : checkVMTrace S s₀ s tr = true := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  simp only [checkVMTrace, h0, h1, Bool.and_eq_true, List.all_eq_true]
  exact ⟨⟨⟨(stateBEq_iff _ _).2 rfl, (stateBEq_iff _ _).2 rfl⟩, checkChain_complete S tr h2⟩,
    fun x hx => (checkVMInvariant_iff S x).2 (h3 x hx)⟩

theorem checkVMTrace_iff (S : VMSpec n) (s₀ s : VMState n) (tr : List (VMState n)) :
    checkVMTrace S s₀ s tr = true ↔ VMCorrect S s₀ s tr :=
  ⟨checkVMTrace_sound S s₀ s tr, checkVMTrace_complete⟩

/-! ### Badges (§3.4) -/

/-- A certified badge: a claim and evidence at level `kernelEstablished`. -/
structure Badge (P : Prop) where
  claim : VerificationClaim
  evidence : Evidence P
  kernel : evidence.assurance = .kernelEstablished

/-- **S1 (badge soundness)**: a badge carries a proof of its proposition. -/
theorem Badge.sound {P : Prop} (b : Badge P) : P := b.evidence.sound b.kernel

/-- The only way to obtain a badge from arbitrary evidence: check its assurance. -/
def Badge.ofEvidence? {P : Prop} (claim : VerificationClaim) (e : Evidence P) :
    Option (Badge P) :=
  if h : e.assurance = .kernelEstablished then some ⟨claim, e, h⟩ else none

theorem Badge.ofEvidence?_isSome_iff {P : Prop} (claim : VerificationClaim) (e : Evidence P) :
    (Badge.ofEvidence? claim e).isSome ↔ e.assurance = .kernelEstablished := by
  unfold Badge.ofEvidence?; split_ifs with h <;> simp [h]

/-- No badge for non-kernel evidence (external executions, imported claims, observations). -/
theorem Badge.ofEvidence?_eq_none {P : Prop} (claim : VerificationClaim) (e : Evidence P)
    (h : e.assurance ≠ .kernelEstablished) : Badge.ofEvidence? claim e = none := by
  simp [Badge.ofEvidence?, h]

/-- Badge from a proof. -/
def Badge.ofProof {P : Prop} (claim : VerificationClaim) (h : P) : Badge P :=
  ⟨claim, .kernel h claim, rfl⟩

/-! ### Trace entries -/

/-- A named, certified trace. -/
structure TraceEntry (S : VMSpec n) where
  name : String
  init : VMState n
  final : VMState n
  tr : List (VMState n)
  correct : VMCorrect S init final tr
  claim : VerificationClaim

namespace TraceEntry

variable {S : VMSpec n}

/-- The evidence of a trace entry (always `kernel`: it carries its proof). -/
def evidence (t : TraceEntry S) : Evidence (VMCorrect S t.init t.final t.tr) :=
  .kernel t.correct t.claim

/-- The assurance of a trace entry, copied from its evidence. -/
def assurance (t : TraceEntry S) : Assurance := t.evidence.assurance

@[simp] theorem assurance_eq (t : TraceEntry S) : t.assurance = .kernelEstablished := rfl

/-- The badge of a trace entry. -/
def badge (t : TraceEntry S) : Badge (VMCorrect S t.init t.final t.tr) :=
  ⟨t.claim, t.evidence, rfl⟩

/-- A trace entry from a closed proof that the checker replays (production `trace`). -/
def ofCheck (name : String) (init final : VMState n) (tr : List (VMState n))
    (h : checkVMTrace S init final tr = true) (claim : VerificationClaim) : TraceEntry S :=
  ⟨name, init, final, tr, checkVMTrace_sound S init final tr h, claim⟩

/-- Run the checker; produce a trace entry only if it replays. -/
def ofCheck? (S : VMSpec n) (name : String) (init final : VMState n) (tr : List (VMState n))
    (claim : VerificationClaim) : Option (TraceEntry S) :=
  if h : checkVMTrace S init final tr = true then some (ofCheck name init final tr h claim)
  else none

theorem ofCheck?_isSome_iff (name : String) (init final : VMState n) (tr : List (VMState n))
    (claim : VerificationClaim) :
    (ofCheck? S name init final tr claim).isSome ↔ VMCorrect S init final tr := by
  rw [← checkVMTrace_iff]; unfold ofCheck?; split_ifs with h <;> simp [h]

/-- Re-checking a certified entry returns it. -/
theorem ofCheck?_self (t : TraceEntry S) :
    ofCheck? S t.name t.init t.final t.tr t.claim = some t := by
  unfold ofCheck?
  rw [dif_pos (checkVMTrace_complete t.correct)]
  rfl

theorem mem_invariant (t : TraceEntry S) {x : VMState n} (hx : x ∈ t.tr) : VMInvariant S x :=
  t.correct.2.2.2 x hx

end TraceEntry

/-- All states of a list of certified traces. -/
def allStates {S : VMSpec n} (traces : List (TraceEntry S)) : List (VMState n) :=
  traces.flatMap TraceEntry.tr

theorem allStates_invariant {S : VMSpec n} (traces : List (TraceEntry S)) :
    ∀ x ∈ allStates traces, VMInvariant S x := by
  intro x hx
  obtain ⟨t, -, hx⟩ := List.mem_flatMap.1 hx
  exact t.mem_invariant hx

/-! ### VM objects -/

/-- A VM object.  `maskHolds` is a hypothesis supplied with the object, never inferred from
`mask.kind`. -/
structure VMObject (n : ℕ) where
  spec : VMSpec n
  obs : Observable
  traces : List (TraceEntry spec)
  mask : Mask
  /-- The order set the mask claims to describe. -/
  omega : Set ℕ
  maskHolds : mask.Holds omega
  provenance : VerificationClaim

namespace VMObject

/-- The object's `omega` is the semantic order set of its spec. -/
def SpecScoped (A : VMObject n) : Prop := A.omega = specOrders A.spec A.obs

/-- The observed mask of the object's certified traces. -/
def observed (A : VMObject n) : Mask :=
  observedMask A.spec A.obs (allStates A.traces) A.provenance.propositionDigest

/-- The observed mask is sound for the semantic order set (no hypothesis needed: it is derived
from certified traces). -/
theorem observed_holds (A : VMObject n) : A.observed.Holds (specOrders A.spec A.obs) :=
  observedMask_holds (allStates_invariant A.traces)

end VMObject

/-- Create a VM object whose mask is the observed mask of its certified traces. -/
def mkVMObject (spec : VMSpec n) (obs : Observable) (traces : List (TraceEntry spec))
    (provenance : VerificationClaim) : VMObject n where
  spec := spec
  obs := obs
  traces := traces
  mask := observedMask spec obs (allStates traces) provenance.propositionDigest
  omega := specOrders spec obs
  maskHolds := observedMask_holds (allStates_invariant traces)
  provenance := provenance

theorem mkVMObject_specScoped (spec : VMSpec n) (obs : Observable)
    (traces : List (TraceEntry spec)) (provenance : VerificationClaim) :
    (mkVMObject spec obs traces provenance).SpecScoped := rfl

@[simp] theorem mkVMObject_mask_kind (spec : VMSpec n) (obs : Observable)
    (traces : List (TraceEntry spec)) (provenance : VerificationClaim) :
    (mkVMObject spec obs traces provenance).mask.kind = .witnessedSubset := rfl

/-- Create a VM object with a declared mask; the hypothesis `h` is supplied by the user. -/
def declareVMObject (spec : VMSpec n) (obs : Observable) (traces : List (TraceEntry spec))
    (mask : Mask) (omega : Set ℕ) (h : mask.Holds omega) (provenance : VerificationClaim) :
    VMObject n :=
  ⟨spec, obs, traces, mask, omega, h, provenance⟩

end Dasein15VM.UI
