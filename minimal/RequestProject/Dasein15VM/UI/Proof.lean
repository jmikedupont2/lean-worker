import RequestProject.Dasein15VM.UI.Guidance

/-!
# RFC-0002 §4.1 / §5: the proof editor and the surface proof grammar

**Proof grammar.**  `ProofTerm n` is the surface syntax

```
proof ::= trace spec init final traceRef | steps spec init [state] | compare maskL maskT
        | compose proof ";" proof
```

with a denotation `ProofTerm.denote` (the proposition a term proves), a `Bool` checker
`ProofTerm.check`, and `ProofTerm.check_sound : p.check = true → p.denote`.  Each production's
soundness is an existing theorem: `trace`/`steps` use `checkVMTrace_sound`, `compare` uses
`compare_contained_sound`/`compare_notContained_sound` (through `compare_verdict`), and
`compose` pairs the two proofs.  A `compare` term whose verdict is `unknown` does **not** check:
`unknown` is never a proof.

`Evidence.both` composes evidence; `Evidence.both_assurance` shows that the composite is
`kernelEstablished` iff both components are.

**Proof editor (Panel A).**  `EditorState` holds a spec, an initial state, a goal state and a
trace being edited.  Badges exist only through the enclosing checker:
`EditorState.stepBadge?_isSome_iff` shows that a per-step badge is available exactly when
`checkVMTrace` replays on the whole trace (obligation **S2**).
-/

namespace Dasein15VM.UI

open SpectrumVM

variable {n : ℕ}

/-! ### Evidence composition -/

/-- Re-index non-kernel evidence (kernel evidence is downgraded to a sound-checker label; this
case is never used by `Evidence.both`). -/
def _root_.SpectrumVM.Evidence.relabel {P Q : Prop} : Evidence P → Evidence Q
  | .observed => .observed
  | .external s h => .external s h
  | .externalExecution c => .externalExecution c
  | .soundChecker c => .soundChecker c
  | .kernel _ c => .soundChecker c

/-- Composite evidence for a conjunction: kernel only when both parts are kernel. -/
def _root_.SpectrumVM.Evidence.both {P Q : Prop} : Evidence P → Evidence Q → Evidence (P ∧ Q)
  | .kernel p c, .kernel q _ => .kernel ⟨p, q⟩ c
  | .kernel _ _, e => e.relabel
  | e, _ => e.relabel

theorem _root_.SpectrumVM.Evidence.both_assurance {P Q : Prop} (e₁ : Evidence P) (e₂ : Evidence Q) :
    (Evidence.both e₁ e₂).assurance = .kernelEstablished ↔
      e₁.assurance = .kernelEstablished ∧ e₂.assurance = .kernelEstablished := by
  cases e₁ <;> cases e₂ <;> simp [Evidence.both, Evidence.relabel, Evidence.assurance]

/-! ### Surface proof terms -/

/-- Surface proof terms. -/
inductive ProofTerm (n : ℕ)
  /-- A certified trace from `init` to `final`. -/
  | trace (S : VMSpec n) (init final : VMState n) (tr : List (VMState n))
  /-- A chain of steps starting at `init`. -/
  | steps (S : VMSpec n) (init : VMState n) (rest : List (VMState n))
  /-- A mask comparison. -/
  | compare (L T : Mask)
  /-- Composition. -/
  | compose (p q : ProofTerm n)

/-- Last state of a `steps` chain. -/
def chainLast (init : VMState n) (rest : List (VMState n)) : VMState n :=
  (init :: rest).getLast (List.cons_ne_nil _ _)

namespace ProofTerm

/-- The proposition proved by a term. -/
def denote : ProofTerm n → Prop
  | .trace S init final tr => VMCorrect S init final tr
  | .steps S init rest => VMCorrect S init (chainLast init rest) (init :: rest)
  | .compare L T => (SpectrumVM.compare L T).status ≠ .unknown ∧
      ∀ ωL ωT : Set ℕ, L.Holds ωL → T.Holds ωT → PosDownset ωT →
        Verdict (SpectrumVM.compare L T) ωL ωT
  | .compose p q => p.denote ∧ q.denote

/-- The checker. -/
def check : ProofTerm n → Bool
  | .trace S init final tr => checkVMTrace S init final tr
  | .steps S init rest => checkVMTrace S init (chainLast init rest) (init :: rest)
  | .compare L T => (SpectrumVM.compare L T).status != .unknown
  | .compose p q => p.check && q.check

/-- **Soundness of the proof grammar.** -/
theorem check_sound : ∀ (p : ProofTerm n), p.check = true → p.denote
  | .trace S init final tr, h => checkVMTrace_sound S init final tr h
  | .steps S init rest, h => checkVMTrace_sound S init _ _ h
  | .compare L T, h => ⟨by simpa [check] using h, fun _ _ hL hT hd => compare_verdict hL hT hd⟩
  | .compose p q, h => by
    simp only [check, Bool.and_eq_true] at h
    exact ⟨check_sound p h.1, check_sound q h.2⟩

/-- Completeness for the VM productions: a correct trace term checks. -/
theorem check_trace_iff (S : VMSpec n) (init final : VMState n) (tr : List (VMState n)) :
    (ProofTerm.trace S init final tr).check = true ↔ (ProofTerm.trace S init final tr).denote :=
  checkVMTrace_iff S init final tr

/-- A `steps` term proves that every listed step is a VM step. -/
theorem steps_denote_step {S : VMSpec n} {init : VMState n} {rest : List (VMState n)}
    (h : (ProofTerm.steps S init rest).denote) :
    ∀ i (hi : i + 1 < (init :: rest).length),
      step S (init :: rest)[i] = some (init :: rest)[i + 1] := h.2.2.1

/-- A checked `compare` term yields a decided (non-`unknown`) verdict. -/
theorem compare_check_decided {L T : Mask} (h : (ProofTerm.compare (n := n) L T).check = true) :
    (SpectrumVM.compare L T).status ≠ .unknown := (check_sound _ h).1

/-- Kernel evidence for a checked term. -/
def toEvidence (p : ProofTerm n) (h : p.check = true) (claim : VerificationClaim) :
    Evidence p.denote :=
  .kernel (check_sound p h) claim

/-- Run the checker; produce a badge only if it passes. -/
def badge? (p : ProofTerm n) (claim : VerificationClaim) : Option (Badge p.denote) :=
  if h : p.check = true then some (Badge.ofProof claim (check_sound p h)) else none

theorem badge?_isSome_iff (p : ProofTerm n) (claim : VerificationClaim) :
    (p.badge? claim).isSome ↔ p.check = true := by
  unfold badge?; split_ifs with h <;> simp [h]

end ProofTerm

/-! ### The proof editor (Panel A) -/

/-- Editor state: a trace under construction. -/
structure EditorState (n : ℕ) where
  spec : VMSpec n
  init : VMState n
  goal : VMState n
  tr : List (VMState n)

namespace EditorState

variable (e : EditorState n)

/-- Append a state. -/
def append (s : VMState n) : EditorState n := { e with tr := e.tr ++ [s] }
/-- Insert a state at a position. -/
def insertAt (i : ℕ) (s : VMState n) : EditorState n := { e with tr := e.tr.insertIdx i s }
/-- Remove the state at a position. -/
def removeAt (i : ℕ) : EditorState n := { e with tr := e.tr.eraseIdx i }
/-- Replace the spec. -/
def setSpec (S : VMSpec n) : EditorState n := { e with spec := S }

/-- Run `checkVMTrace` on the edited trace. -/
def replays : Bool := checkVMTrace e.spec e.init e.goal e.tr

/-- The trace badge, available only when the checker replays. -/
def traceBadge? (claim : VerificationClaim) : Option (Badge (VMCorrect e.spec e.init e.goal e.tr)) :=
  if h : e.replays = true then some (Badge.ofProof claim (checkVMTrace_sound _ _ _ _ h)) else none

/-- The per-step badge for step `i`, derived from the enclosing trace check. -/
def stepBadge? (i : ℕ) (claim : VerificationClaim) :
    Option (Badge (∃ h : i + 1 < e.tr.length, step e.spec e.tr[i] = some e.tr[i + 1])) :=
  if h : e.replays = true ∧ i + 1 < e.tr.length then
    some (Badge.ofProof claim ⟨h.2, (checkVMTrace_sound _ _ _ _ h.1).2.2.1 i h.2⟩)
  else none

/-- **S2**: a step shows `kernel` exactly when the enclosing `checkVMTrace` replays (and the step
exists). -/
theorem stepBadge?_isSome_iff (i : ℕ) (claim : VerificationClaim) :
    (e.stepBadge? i claim).isSome ↔ checkVMTrace e.spec e.init e.goal e.tr = true ∧
      i + 1 < e.tr.length := by
  unfold stepBadge? replays at *; split_ifs with h <;> simp_all

theorem traceBadge?_isSome_iff (claim : VerificationClaim) :
    (e.traceBadge? claim).isSome ↔ VMCorrect e.spec e.init e.goal e.tr := by
  unfold traceBadge?
  split_ifs with h
  · simpa using checkVMTrace_sound _ _ _ _ h
  · simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    exact fun hc => h (checkVMTrace_complete hc)

/-- Commit the edited trace as a certified trace entry (only if it replays). -/
def commit? (name : String) (claim : VerificationClaim) : Option (TraceEntry e.spec) :=
  TraceEntry.ofCheck? e.spec name e.init e.goal e.tr claim

/-- The editor's trace as a proof term. -/
def toProofTerm : ProofTerm n := .trace e.spec e.init e.goal e.tr

end EditorState

end Dasein15VM.UI
