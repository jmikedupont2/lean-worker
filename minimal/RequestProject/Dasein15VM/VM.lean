import RequestProject.Dasein15VM.Fractran
import RequestProject.SpectrumVM.Bundle

/-!
# Dasein15 VM, phases 2–4: state, shape-dispatched step, trust, trace correctness

* `VMSpec n`: a prime basis, a class assignment, a *dispatch table* `route : ShapeClass → route`
  (each shape class runs its own FRACTRAN program `S.program e`), and the conserved mass.
* `VMState n`: `config` (the FRACTRAN Gödel number), `steps`, `shape`, `cls`.
* `VMInvariant S s`: `config = godel shape`, `cls = shapeClass shape`, `mass shape = S.mass`.
  `checkVMInvariant` is its `Bool` checker, with `checkVMInvariant_sound`.
* `step S s`: dispatch on `s.cls`, apply that class's routed transition, re-derive shape/class
  and gate the result with `checkVMInvariant`.
  - `step_preserves_invariant`: every produced state satisfies the invariant;
  - `step_isSome`: on an invariant state of positive mass the gate never fires;
  - `step_fractran`: on an invariant state, `step` is exactly one FRACTRAN step of the
    class's program on the Gödel number.
* Trust (SpectrumVM's `Evidence`): `CertState S` pairs a state with `Evidence (VMInvariant S _)`;
  `certStep` produces `kernel` evidence; `stepEvidence` is the per-step evidence.
* `VMCorrect` (trace-indexed analogue of `BundleCorrect`), the `Bool` checker `checkVMTrace`
  and `checkVMTrace_sound`.
-/

namespace Dasein15VM

open SpectrumVM (Evidence Assurance VerificationClaim)

variable {n : ℕ}

/-- A shape-dispatched VM specification. -/
structure VMSpec (n : ℕ) where
  basis : PrimeBasis n
  assign : Fin n → ShapeClass
  /-- Dispatch table: the route used by each shape class. -/
  route : ShapeClass → Fin n → Fin n
  route_ne : ∀ e i, route e i ≠ i
  /-- The conserved total mass. -/
  mass : ℕ

/-- VM state. -/
structure VMState (n : ℕ) where
  config : ℕ
  steps : ℕ
  shape : PrimeShape n
  cls : ShapeClass

namespace VMSpec

variable (S : VMSpec n)

/-- The FRACTRAN program run by the shape class `e`. -/
def program (e : ShapeClass) : List ℚ := routeProg S.basis (S.route e)

/-- The state determined by a shape. -/
def ofShape (v : PrimeShape n) (k : ℕ) : VMState n :=
  ⟨godel S.basis v, k, v, shapeClass S.assign v⟩

end VMSpec

/-- The VM invariant. -/
def VMInvariant (S : VMSpec n) (s : VMState n) : Prop :=
  s.config = godel S.basis s.shape ∧ s.cls = shapeClass S.assign s.shape ∧
    mass s.shape = S.mass

/-- `Bool` checker for the invariant. -/
def checkVMInvariant (S : VMSpec n) (s : VMState n) : Bool :=
  s.config == godel S.basis s.shape && s.cls == shapeClass S.assign s.shape &&
    mass s.shape == S.mass

theorem checkVMInvariant_iff (S : VMSpec n) (s : VMState n) :
    checkVMInvariant S s = true ↔ VMInvariant S s := by
  simp [checkVMInvariant, VMInvariant, and_assoc]

/-- **Checker soundness.** -/
theorem checkVMInvariant_sound (S : VMSpec n) (s : VMState n) (h : checkVMInvariant S s = true) :
    VMInvariant S s := (checkVMInvariant_iff S s).1 h

/-- Under the invariant, the stored shape is the exponent vector of the configuration. -/
theorem VMInvariant.shapeOf_config {S : VMSpec n} {s : VMState n} (h : VMInvariant S s) :
    shapeOf S.basis s.config = s.shape := by
  rw [h.1, shapeOf_godel]

/-- One VM step: dispatch on the shape class, apply that class's transition, re-derive the shape
and class, and gate the result with the invariant checker. -/
def step (S : VMSpec n) (s : VMState n) : Option (VMState n) :=
  match routeStep (S.route s.cls) s.shape with
  | none => none
  | some v => if checkVMInvariant S (S.ofShape v (s.steps + 1)) then
      some (S.ofShape v (s.steps + 1)) else none

theorem step_eq_some {S : VMSpec n} {s s' : VMState n} (h : step S s = some s') :
    ∃ v, routeStep (S.route s.cls) s.shape = some v ∧ s' = S.ofShape v (s.steps + 1) ∧
      checkVMInvariant S s' = true := by
  unfold step at h
  split at h
  · simp at h
  · rename_i v hv
    split_ifs at h with hc
    · cases h; exact ⟨v, hv, rfl, hc⟩

/-- **Step soundness**: every state produced by `step` satisfies the invariant. -/
theorem step_preserves_invariant (S : VMSpec n) {s s' : VMState n} (h : step S s = some s') :
    VMInvariant S s' := by
  obtain ⟨v, -, -, hc⟩ := step_eq_some h
  exact checkVMInvariant_sound S s' hc

theorem step_steps {S : VMSpec n} {s s' : VMState n} (h : step S s = some s') :
    s'.steps = s.steps + 1 := by
  obtain ⟨v, -, rfl, -⟩ := step_eq_some h; rfl

/-- On an invariant state, `step` is the routed transition (the gate always passes). -/
theorem step_of_invariant (S : VMSpec n) {s : VMState n} (hs : VMInvariant S s) :
    step S s = (routeStep (S.route s.cls) s.shape).map fun v => S.ofShape v (s.steps + 1) := by
  unfold step
  split
  · next h => rw [h]; rfl
  · next v hv =>
    rw [hv, if_pos]; · rfl
    rw [checkVMInvariant_iff]
    refine ⟨rfl, rfl, ?_⟩
    exact (mass_routeStep _ hv).trans hs.2.2

/-- **Liveness**: an invariant state of positive mass always steps (the gate never halts it). -/
theorem step_isSome (S : VMSpec n) (hm : 0 < S.mass) {s : VMState n} (hs : VMInvariant S s) :
    (step S s).isSome := by
  rw [step_of_invariant S hs, Option.isSome_map]
  exact routeStep_isSome _ (hs.2.2 ▸ hm)

/-- **FRACTRAN agreement**: on an invariant state, one VM step is exactly one FRACTRAN step of the
program dispatched by the current shape class, acting on the Gödel number. -/
theorem step_fractran (S : VMSpec n) {s : VMState n} (hs : VMInvariant S s) :
    fractranStep (S.program s.cls) s.config = (step S s).map VMState.config := by
  rw [step_of_invariant S hs, hs.1, VMSpec.program,
    fractranStep_routeProg _ _ (S.route_ne s.cls), Option.map_map]
  rfl

/-! ### Trust integration (SpectrumVM `Evidence`) -/

/-- A VM state together with evidence for its invariant. -/
structure CertState (S : VMSpec n) where
  state : VMState n
  trust : Evidence (VMInvariant S state)

/-- Per-step evidence: from evidence-free knowledge that `s` is invariant and that `step s = s'`,
kernel evidence for the invariant before and after. -/
def stepEvidence (S : VMSpec n) {s s' : VMState n} (hs : VMInvariant S s)
    (h : step S s = some s') (claim : VerificationClaim) :
    Evidence (VMInvariant S s ∧ VMInvariant S s') :=
  .kernel ⟨hs, step_preserves_invariant S h⟩ claim

/-- Certified step: the new state carries kernel evidence for its invariant. -/
def certStep (S : VMSpec n) (claim : VerificationClaim) (c : CertState S) :
    Option (CertState S) :=
  match h : step S c.state with
  | none => none
  | some s' => some ⟨s', .kernel (step_preserves_invariant S h) claim⟩

theorem certStep_state (S : VMSpec n) (claim : VerificationClaim) (c : CertState S) :
    (certStep S claim c).map CertState.state = step S c.state := by
  unfold certStep
  split <;> simp_all

theorem certStep_assurance (S : VMSpec n) (claim : VerificationClaim) {c c' : CertState S}
    (h : certStep S claim c = some c') : c'.trust.assurance = .kernelEstablished := by
  unfold certStep at h
  split at h
  · simp at h
  · cases h; rfl

/-! ### Trace correctness -/

/-- **Trace correctness**: the trace starts at `s₀`, ends at `s`, each consecutive pair is a VM
step, and every state satisfies the invariant. -/
def VMCorrect (S : VMSpec n) (s₀ s : VMState n) (tr : List (VMState n)) : Prop :=
  tr.head? = some s₀ ∧ tr.getLast? = some s ∧
    (∀ i (h : i + 1 < tr.length), step S tr[i] = some tr[i + 1]) ∧
    ∀ s' ∈ tr, VMInvariant S s'

/-- Boolean equality of shapes. -/
def shapeBEq (v w : PrimeShape n) : Bool := (List.finRange n).all fun i => v i == w i

theorem shapeBEq_iff (v w : PrimeShape n) : shapeBEq v w = true ↔ v = w := by
  simp [shapeBEq, funext_iff]

/-- Boolean equality of states. -/
def stateBEq (s t : VMState n) : Bool :=
  s.config == t.config && s.steps == t.steps && shapeBEq s.shape t.shape && s.cls == t.cls

theorem stateBEq_iff (s t : VMState n) : stateBEq s t = true ↔ s = t := by
  cases s; cases t
  simp [stateBEq, shapeBEq_iff, and_assoc]

/-- `Bool` check that `t` is the VM successor of `s`. -/
def checkStep (S : VMSpec n) (s t : VMState n) : Bool :=
  match step S s with
  | some t' => stateBEq t' t
  | none => false

theorem checkStep_iff (S : VMSpec n) (s t : VMState n) :
    checkStep S s t = true ↔ step S s = some t := by
  unfold checkStep
  split <;> simp_all [stateBEq_iff]

/-- `Bool` check that consecutive states are VM steps. -/
def checkChain (S : VMSpec n) : List (VMState n) → Bool
  | s :: t :: rest => checkStep S s t && checkChain S (t :: rest)
  | _ => true

theorem checkChain_sound (S : VMSpec n) :
    ∀ (l : List (VMState n)), checkChain S l = true →
      ∀ i (h : i + 1 < l.length), step S l[i] = some l[i + 1]
  | [], _, i, h => by simp at h
  | [_], _, i, h => by simp at h
  | s :: t :: rest, hc, i, h => by
    simp only [checkChain, Bool.and_eq_true] at hc
    rcases i with _ | i
    · exact (checkStep_iff S s t).1 hc.1
    · exact checkChain_sound S (t :: rest) hc.2 i (by simp at h ⊢; omega)

/-- The tr checker. -/
def checkVMTrace (S : VMSpec n) (s₀ s : VMState n) (tr : List (VMState n)) : Bool :=
  (match tr.head? with | some a => stateBEq a s₀ | none => false) &&
  (match tr.getLast? with | some a => stateBEq a s | none => false) &&
  checkChain S tr && tr.all (checkVMInvariant S)

/-- **Trace checker soundness.** -/
theorem checkVMTrace_sound (S : VMSpec n) (s₀ s : VMState n) (tr : List (VMState n))
    (h : checkVMTrace S s₀ s tr = true) : VMCorrect S s₀ s tr := by
  simp only [checkVMTrace, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
  refine ⟨?_, ?_, checkChain_sound S tr h2, fun s' hs' => checkVMInvariant_sound S s' (h3 s' hs')⟩
  · revert h0; cases tr.head? <;> simp [stateBEq_iff]
  · revert h1; cases tr.getLast? <;> simp [stateBEq_iff]

/-- Kernel evidence for trace correctness from a closed proof of the checker. -/
def traceEvidence (S : VMSpec n) (s₀ s : VMState n) (tr : List (VMState n))
    (h : checkVMTrace S s₀ s tr = true) (claim : VerificationClaim) :
    Evidence (VMCorrect S s₀ s tr) :=
  .kernel (checkVMTrace_sound S s₀ s tr h) claim

/-- A correct tr of a VM whose dispatch table is constant is a FRACTRAN run of that single
program: `tr.length - 1` FRACTRAN steps take `s₀.config` to `s.config`. -/
theorem VMCorrect.fractranRun {S : VMSpec n} {τ : Fin n → Fin n} (hτ : ∀ e, S.route e = τ)
    {s₀ s : VMState n} {tr : List (VMState n)} (h : VMCorrect S s₀ s tr) :
    fractranRun (routeProg S.basis τ) (tr.length - 1) s₀.config = some s.config := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  induction tr generalizing s₀ with
  | nil => simp at h0
  | cons a rest ih =>
    simp only [List.head?_cons, Option.some.injEq] at h0
    subst h0
    rcases rest with _ | ⟨b, rest⟩
    · simp at h1; subst h1; rfl
    · have hab : step S a = some b := h2 0 (by simp)
      have hfr := step_fractran S (h3 a (by simp))
      rw [hab, VMSpec.program, hτ] at hfr
      have := ih (s₀ := b) rfl (by simpa using h1)
        (fun i hi => h2 (i + 1) (by simp at hi ⊢; omega))
        (fun s' hs' => h3 s' (by simp [hs']))
      simp only [List.length_cons, Nat.add_sub_cancel] at this ⊢
      rw [Dasein15VM.fractranRun, hfr]
      simpa using this

/-- Unbounded mass conservation for routed FRACTRAN programs: from the Gödel number of a shape of
positive mass, every number of steps succeeds and lands on the Gödel number of a shape of the same
mass. -/
theorem fractranRun_routeProg_mass (B : PrimeBasis n) (τ : Fin n → Fin n) (hτ : ∀ i, τ i ≠ i) :
    ∀ (k : ℕ) (v : PrimeShape n), 0 < mass v →
      ∃ w, fractranRun (routeProg B τ) k (godel B v) = some (godel B w) ∧ mass w = mass v
  | 0, v, _ => ⟨v, rfl, rfl⟩
  | k + 1, v, hv => by
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 (routeStep_isSome τ hv)
    have hm := mass_routeStep τ hw
    obtain ⟨u, hu, hmu⟩ := fractranRun_routeProg_mass B τ hτ k w (hm ▸ hv)
    refine ⟨u, ?_, hmu.trans hm⟩
    rw [fractranRun, fractranStep_routeProg B τ hτ, hw]
    exact hu

end Dasein15VM
