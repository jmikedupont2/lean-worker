import RequestProject.Dasein15VM.VM

/-!
# Dasein15 VM with Hecke arguments: steps that are allowed to expand

The plain Dasein15 VM conserves mass exactly, so it can never apply a Hecke operator `T_p`
(which multiplies the FRACTRAN state by `p` and raises the mass by one). This file lets each step
take a **Hecke argument**, controlled by a **Hecke policy** passed to the trace checker.

* `HeckeArg n`: an exponent vector `d`. As an argument it acts as the Hecke operator `T_m` with
  `m = godel B d = ∏ pᵢ ^ dᵢ`: the state is multiplied by `m` (exponents add,
  `godel_add_hecke`) and the mass grows by `mass d` (`mass_add`). `HeckeArg.T i` is the single operator `T_{pᵢ}`
  (`godel_T`, `mass_T`), and `0` means "no Hecke operator".
* `HeckePolicy n`: which primes may be used (`allowed`) and the total expansion `budget` of a
  run. `HeckePolicy.conserve` allows nothing and has budget 0.
* `heckeStep S P d s`: if `P` admits `d`, first apply `T_m` to the shape, then re-derive the
  class of the expanded shape, run that class's routed transition and gate the result with a `Bool`
  invariant checker at the new mass.
  - `heckeStep_preserves`: an invariant state of mass `m` steps to an invariant state of mass
    `m + mass d`;
  - `heckeStep_fractran`: on an invariant state, `heckeStep` is "multiply the Gödel number by
    `m`, then one FRACTRAN step of the program of the class of the expanded shape";
  - `heckeStep_isSome`: the gate never fires on an invariant state of positive resulting mass;
  - `heckeStep_zero`: with argument `0` it is exactly the old `step`.
* `HeckeCorrect S P s₀ s args tr`: the trace-indexed correctness predicate, with checker
  `checkHeckeTrace` and soundness `checkHeckeTrace_sound`, plus kernel `Evidence`.
  - `HeckeCorrect.final_invariant`: the final state is invariant at mass
    `S.mass + totalArgMass args`, which lies between `S.mass` and `S.mass + P.budget`;
  - `HeckeCorrect.mem_invariant`: every state of the trace is invariant at some mass in that band;
  - `HeckeCorrect.of_VMCorrect`: every certified run of the old VM is a Hecke run with all
    arguments `0`, under any policy;
  - `HeckeCorrect.toVMCorrect`: with budget `0` a Hecke run is a run of the old VM. So budget 0
    gives back the conserving VM exactly.
-/

namespace Dasein15VM

open SpectrumVM (Evidence VerificationClaim)

variable {n : ℕ}

/-! ## Hecke arguments and policies -/

/-- A Hecke argument `d`: it acts as `T_m` with `m = ∏ pᵢ ^ dᵢ` (`0` = no Hecke operator). -/
abbrev HeckeArg (n : ℕ) := PrimeShape n

/-- The single Hecke operator `T_{pᵢ}`. -/
def HeckeArg.T (i : Fin n) : HeckeArg n := Pi.single i 1

/-- A Hecke policy: which primes may be used, and the total expansion allowed in a run. -/
structure HeckePolicy (n : ℕ) where
  allowed : Fin n → Bool
  budget : ℕ

/-- The conserving policy: no Hecke operator, budget `0`. -/
def HeckePolicy.conserve : HeckePolicy n := ⟨fun _ => false, 0⟩

/-- The policy allowing every prime, with budget `b`. -/
def HeckePolicy.all (b : ℕ) : HeckePolicy n := ⟨fun _ => true, b⟩

/-- `P` admits `d` when `d` only uses allowed primes. -/
def HeckePolicy.admits (P : HeckePolicy n) (d : HeckeArg n) : Bool :=
  (List.finRange n).all fun i => d i == 0 || P.allowed i

theorem HeckePolicy.admits_iff (P : HeckePolicy n) (d : HeckeArg n) :
    P.admits d = true ↔ ∀ i, d i ≠ 0 → P.allowed i = true := by
  simp only [admits, List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true,
    beq_iff_eq]
  exact forall_congr' fun i => by tauto

@[simp] theorem HeckePolicy.admits_zero (P : HeckePolicy n) : P.admits 0 = true := by
  simp [admits]

theorem HeckePolicy.admits_T (P : HeckePolicy n) (i : Fin n) :
    P.admits (HeckeArg.T i) = P.allowed i := by
  cases h : P.allowed i
  · apply Bool.eq_false_iff.2
    intro hc
    have := (P.admits_iff _).1 hc i (by simp [HeckeArg.T])
    simp_all
  · refine (P.admits_iff _).2 fun j hj => ?_
    by_cases hji : j = i
    · subst hji; exact h
    · simp [HeckeArg.T, hji] at hj

/-! ## Effect of a Hecke argument on mass and Gödel number -/

theorem mass_add (v d : PrimeShape n) : mass (v + d) = mass v + mass d := by
  simp [mass_eq_sum, Finset.sum_add_distrib]

@[simp] theorem mass_zero : mass (0 : PrimeShape n) = 0 := by simp [mass_eq_sum]

theorem mass_eq_zero_iff (d : PrimeShape n) : mass d = 0 ↔ d = 0 := by
  rw [mass_eq_sum, Finset.sum_eq_zero_iff]
  simp [funext_iff]

/-- Applying the argument `d` multiplies the Gödel number by `godel B d`. -/
theorem godel_add_hecke (B : PrimeBasis n) (v d : PrimeShape n) :
    godel B (v + d) = godel B v * godel B d := by
  simp [godel_eq_prod, pow_add, Finset.prod_mul_distrib]

theorem mass_T (i : Fin n) : mass (HeckeArg.T i) = 1 := by
  simp [mass_eq_sum, HeckeArg.T]

/-- `T_{pᵢ}` multiplies the Gödel number by `pᵢ`. -/
theorem godel_T (B : PrimeBasis n) (i : Fin n) : godel B (HeckeArg.T i) = B.p i := by
  rw [godel_eq_prod, Finset.prod_eq_single i]
  · simp [HeckeArg.T]
  · intro j _ hj; simp [HeckeArg.T, hj]
  · simp

/-! ## The invariant at a given mass -/

/-- The VM invariant with the mass as a parameter. -/
def InvAt (S : VMSpec n) (m : ℕ) (s : VMState n) : Prop :=
  s.config = godel S.basis s.shape ∧ s.cls = shapeClass S.assign s.shape ∧ mass s.shape = m

/-- `Bool` checker for `InvAt`. -/
def checkInvAt (S : VMSpec n) (m : ℕ) (s : VMState n) : Bool :=
  s.config == godel S.basis s.shape && s.cls == shapeClass S.assign s.shape && mass s.shape == m

theorem checkInvAt_iff (S : VMSpec n) (m : ℕ) (s : VMState n) :
    checkInvAt S m s = true ↔ InvAt S m s := by
  simp [checkInvAt, InvAt, and_assoc]

/-- At the spec's own mass, `InvAt` is the old invariant. -/
theorem invAt_mass_iff (S : VMSpec n) (s : VMState n) : InvAt S S.mass s ↔ VMInvariant S s :=
  Iff.rfl

theorem InvAt.mass_eq {S : VMSpec n} {m : ℕ} {s : VMState n} (h : InvAt S m s) :
    mass s.shape = m := h.2.2

/-! ## The Hecke step -/

/-- One VM step with Hecke argument `d` under policy `P`: check that `P` admits `d`, apply `T_m`
(`m = godel B d`) to the shape, dispatch on the class of the expanded shape, run that class's
routed transition, and gate the result with the invariant checker at the new mass. -/
def heckeStep (S : VMSpec n) (P : HeckePolicy n) (d : HeckeArg n) (s : VMState n) :
    Option (VMState n) :=
  if P.admits d then
    match routeStep (S.route (shapeClass S.assign (s.shape + d))) (s.shape + d) with
    | none => none
    | some w => if checkInvAt S (mass s.shape + mass d) (S.ofShape w (s.steps + 1)) then
        some (S.ofShape w (s.steps + 1)) else none
  else none

theorem heckeStep_eq_some {S : VMSpec n} {P : HeckePolicy n} {d : HeckeArg n} {s s' : VMState n}
    (h : heckeStep S P d s = some s') :
    P.admits d = true ∧ ∃ w, routeStep (S.route (shapeClass S.assign (s.shape + d)))
      (s.shape + d) = some w ∧ s' = S.ofShape w (s.steps + 1) ∧
      checkInvAt S (mass s.shape + mass d) s' = true := by
  unfold heckeStep at h
  split_ifs at h with hP
  refine ⟨hP, ?_⟩
  split at h
  · simp at h
  · rename_i w hw
    split_ifs at h with hc
    cases h
    exact ⟨w, hw, rfl, hc⟩

/-- **Hecke step soundness**: from an invariant state of mass `m`, a Hecke step with argument `d`
lands on an invariant state of mass `m + mass d`. -/
theorem heckeStep_preserves (S : VMSpec n) (P : HeckePolicy n) {d : HeckeArg n} {m : ℕ}
    {s s' : VMState n} (hs : InvAt S m s) (h : heckeStep S P d s = some s') :
    InvAt S (m + mass d) s' := by
  obtain ⟨-, w, -, -, hc⟩ := heckeStep_eq_some h
  rw [← hs.mass_eq]
  exact (checkInvAt_iff _ _ _).1 hc

theorem heckeStep_steps {S : VMSpec n} {P : HeckePolicy n} {d : HeckeArg n} {s s' : VMState n}
    (h : heckeStep S P d s = some s') : s'.steps = s.steps + 1 := by
  obtain ⟨-, w, -, rfl, -⟩ := heckeStep_eq_some h; rfl

/-- A Hecke step only uses admitted arguments. -/
theorem heckeStep_admits {S : VMSpec n} {P : HeckePolicy n} {d : HeckeArg n} {s s' : VMState n}
    (h : heckeStep S P d s = some s') : P.admits d = true := (heckeStep_eq_some h).1

/-- On an admitted argument, `heckeStep` is the routed transition of the expanded shape. -/
theorem heckeStep_of_admits (S : VMSpec n) {P : HeckePolicy n} {d : HeckeArg n}
    (hP : P.admits d = true) (s : VMState n) :
    heckeStep S P d s = (routeStep (S.route (shapeClass S.assign (s.shape + d)))
      (s.shape + d)).map fun w => S.ofShape w (s.steps + 1) := by
  unfold heckeStep
  rw [if_pos hP]
  split
  · next h => rw [h]; rfl
  · next w hw =>
    rw [hw, if_pos]; · rfl
    rw [checkInvAt_iff]
    refine ⟨rfl, rfl, ?_⟩
    exact (mass_routeStep _ hw).trans (mass_add _ _)

/-- **Liveness**: the gate never halts an admitted step whose resulting mass is positive. -/
theorem heckeStep_isSome (S : VMSpec n) {P : HeckePolicy n} {d : HeckeArg n}
    (hP : P.admits d = true) (s : VMState n) (hm : 0 < mass s.shape + mass d) :
    (heckeStep S P d s).isSome := by
  rw [heckeStep_of_admits S hP, Option.isSome_map]
  exact routeStep_isSome _ (by rwa [mass_add])

/-- Arguments the policy does not admit are rejected. -/
theorem heckeStep_not_admits (S : VMSpec n) {P : HeckePolicy n} {d : HeckeArg n}
    (hP : P.admits d = false) (s : VMState n) : heckeStep S P d s = none := by
  simp [heckeStep, hP]

/-- **FRACTRAN agreement**: on an invariant state, an admitted Hecke step multiplies the Gödel
number by `m = godel B d` and then makes one FRACTRAN step of the program dispatched by the class of
the expanded shape. -/
theorem heckeStep_fractran (S : VMSpec n) {P : HeckePolicy n} {d : HeckeArg n} {m : ℕ}
    (hP : P.admits d = true) {s : VMState n} (hs : InvAt S m s) :
    fractranStep (S.program (shapeClass S.assign (s.shape + d))) (s.config * godel S.basis d) =
      (heckeStep S P d s).map VMState.config := by
  rw [heckeStep_of_admits S hP, hs.1, ← godel_add_hecke, VMSpec.program,
    fractranStep_routeProg _ _ (S.route_ne _), Option.map_map]
  rfl

/-- **Conservative extension**: with argument `0`, on an invariant state, a Hecke step is the old
VM step. -/
theorem heckeStep_zero (S : VMSpec n) (P : HeckePolicy n) {s : VMState n}
    (hs : VMInvariant S s) : heckeStep S P 0 s = step S s := by
  rw [heckeStep_of_admits S (P.admits_zero), step_of_invariant S hs, add_zero, ← hs.2.1]

/-! ## Traces with Hecke arguments -/

/-- Total expansion of a list of arguments. -/
def totalArgMass (args : List (HeckeArg n)) : ℕ := (args.map mass).sum

@[simp] theorem totalArgMass_nil : totalArgMass ([] : List (HeckeArg n)) = 0 := rfl

@[simp] theorem totalArgMass_cons (d : HeckeArg n) (ds : List (HeckeArg n)) :
    totalArgMass (d :: ds) = mass d + totalArgMass ds := rfl

theorem totalArgMass_eq_zero_iff (args : List (HeckeArg n)) :
    totalArgMass args = 0 ↔ ∀ d ∈ args, d = 0 := by
  induction args with
  | nil => simp
  | cons d ds ih => simp [ih, mass_eq_zero_iff]

/-- The arguments `args` drive the states `tr`: `tr` has one more state than `args` has
arguments, and the `i`-th state steps to the `(i+1)`-th with the `i`-th argument. -/
def HeckeChain (S : VMSpec n) (P : HeckePolicy n) :
    List (HeckeArg n) → List (VMState n) → Prop
  | [], [_] => True
  | d :: ds, s :: t :: rest => heckeStep S P d s = some t ∧ HeckeChain S P ds (t :: rest)
  | _, _ => False

/-- **Trace correctness with Hecke arguments**: `tr` starts at the invariant state `s₀`, ends at
`s`, is driven by `args` under the policy `P`, and the total expansion is within `P.budget`. -/
def HeckeCorrect (S : VMSpec n) (P : HeckePolicy n) (s₀ s : VMState n)
    (args : List (HeckeArg n)) (tr : List (VMState n)) : Prop :=
  tr.head? = some s₀ ∧ tr.getLast? = some s ∧ HeckeChain S P args tr ∧ VMInvariant S s₀ ∧
    totalArgMass args ≤ P.budget

theorem HeckeChain.length {S : VMSpec n} {P : HeckePolicy n} :
    ∀ {args : List (HeckeArg n)} {tr : List (VMState n)}, HeckeChain S P args tr →
      tr.length = args.length + 1
  | [], [_], _ => rfl
  | _ :: _, _ :: _ :: _, h => by
    simpa using HeckeChain.length (args := _) (tr := _ :: _) h.2
  | [], [], h | [], _ :: _ :: _, h | _ :: _, [], h | _ :: _, [_], h => h.elim

/-- Along a chain from a state invariant at mass `m`, the last state is invariant at mass
`m + totalArgMass args`, and every state is invariant at a mass between `m` and that. -/
theorem HeckeChain.invariant {S : VMSpec n} {P : HeckePolicy n} :
    ∀ {args : List (HeckeArg n)} {tr : List (VMState n)} {m : ℕ} {a : VMState n},
      HeckeChain S P args tr → tr.head? = some a → InvAt S m a →
      (∀ z, tr.getLast? = some z → InvAt S (m + totalArgMass args) z) ∧
      ∀ x ∈ tr, ∃ k, m ≤ k ∧ k ≤ m + totalArgMass args ∧ InvAt S k x
  | [], [b], m, a, _, h0, ha => by
    simp only [List.head?_cons, Option.some.injEq] at h0
    subst h0
    refine ⟨fun z hz => ?_, fun x hx => ?_⟩
    · simp only [List.getLast?_singleton, Option.some.injEq] at hz
      subst hz; simpa using ha
    · simp only [List.mem_singleton] at hx
      subst hx; exact ⟨m, le_rfl, by simp, ha⟩
  | d :: ds, b :: t :: rest, m, a, h, h0, ha => by
    simp only [List.head?_cons, Option.some.injEq] at h0
    subst h0
    have ht := heckeStep_preserves S P ha h.1
    obtain ⟨ih1, ih2⟩ := HeckeChain.invariant (tr := t :: rest) h.2 rfl ht
    refine ⟨fun z hz => ?_, fun x hx => ?_⟩
    · have := ih1 z (by simpa [List.getLast?_cons_cons] using hz)
      simpa [add_assoc] using this
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨m, le_rfl, by simp, ha⟩
      · obtain ⟨k, hk1, hk2, hk⟩ := ih2 x hx
        exact ⟨k, by omega, by simp only [totalArgMass_cons]; omega, hk⟩
  | [], [], _, _, h, _, _ | [], _ :: _ :: _, _, _, h, _, _ | _ :: _, [], _, _, h, _, _
  | _ :: _, [_], _, _, h, _, _ => h.elim

/-- The final state of a correct Hecke run is invariant at mass `S.mass + totalArgMass args`. -/
theorem HeckeCorrect.final_invariant {S : VMSpec n} {P : HeckePolicy n} {s₀ s : VMState n}
    {args : List (HeckeArg n)} {tr : List (VMState n)} (h : HeckeCorrect S P s₀ s args tr) :
    InvAt S (S.mass + totalArgMass args) s :=
  (h.2.2.1.invariant h.1 h.2.2.2.1).1 s h.2.1

/-- The final mass of a correct Hecke run lies between `S.mass` and `S.mass + P.budget`. -/
theorem HeckeCorrect.final_mass_le {S : VMSpec n} {P : HeckePolicy n} {s₀ s : VMState n}
    {args : List (HeckeArg n)} {tr : List (VMState n)} (h : HeckeCorrect S P s₀ s args tr) :
    S.mass ≤ mass s.shape ∧ mass s.shape ≤ S.mass + P.budget := by
  have := h.final_invariant.mass_eq
  have := h.2.2.2.2
  omega

/-- Every state of a correct Hecke run is invariant at some mass in `[S.mass, S.mass + P.budget]`. -/
theorem HeckeCorrect.mem_invariant {S : VMSpec n} {P : HeckePolicy n} {s₀ s : VMState n}
    {args : List (HeckeArg n)} {tr : List (VMState n)} (h : HeckeCorrect S P s₀ s args tr) :
    ∀ x ∈ tr, ∃ k, S.mass ≤ k ∧ k ≤ S.mass + P.budget ∧ InvAt S k x := by
  intro x hx
  obtain ⟨k, hk1, hk2, hk⟩ := (h.2.2.1.invariant h.1 h.2.2.2.1).2 x hx
  exact ⟨k, hk1, by have := h.2.2.2.2; omega, hk⟩

/-- Every argument of a correct Hecke run is admitted by the policy. -/
theorem HeckeChain.admits {S : VMSpec n} {P : HeckePolicy n} :
    ∀ {args : List (HeckeArg n)} {tr : List (VMState n)}, HeckeChain S P args tr →
      ∀ d ∈ args, P.admits d = true
  | [], _, _, d, hd => by simp at hd
  | _ :: _, _ :: _ :: _, h, d, hd => by
    rcases List.mem_cons.1 hd with rfl | hd
    · exact heckeStep_admits h.1
    · exact HeckeChain.admits (tr := _ :: _) h.2 d hd
  | _ :: _, [], h, _, _ | _ :: _, [_], h, _, _ => h.elim

/-! ### Relation with the conserving VM -/

/-- Zero arguments along an old-VM chain give a Hecke chain. -/
theorem heckeChain_of_steps (S : VMSpec n) (P : HeckePolicy n) :
    ∀ (tr : List (VMState n)), tr ≠ [] → (∀ i (h : i + 1 < tr.length), step S tr[i] = some tr[i + 1]) →
      (∀ s' ∈ tr, VMInvariant S s') → HeckeChain S P (List.replicate (tr.length - 1) 0) tr
  | [], h, _, _ => (h rfl).elim
  | [_], _, _, _ => trivial
  | a :: b :: rest, _, hst, hinv => by
    refine ⟨?_, ?_⟩
    · rw [heckeStep_zero S P (hinv a (by simp))]
      exact hst 0 (by simp)
    · have := heckeChain_of_steps S P (b :: rest) (by simp)
        (fun i hi => hst (i + 1) (by simp at hi ⊢; omega))
        (fun s' hs' => hinv s' (by simp [hs']))
      simpa using this

/-- **The old VM embeds**: every correct run of the conserving VM is a correct Hecke run with all
arguments `0`, under any policy. -/
theorem HeckeCorrect.of_VMCorrect {S : VMSpec n} (P : HeckePolicy n) {s₀ s : VMState n}
    {tr : List (VMState n)} (h : VMCorrect S s₀ s tr) :
    HeckeCorrect S P s₀ s (List.replicate (tr.length - 1) 0) tr := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  have hne : tr ≠ [] := by rintro rfl; simp at h0
  refine ⟨h0, h1, heckeChain_of_steps S P tr hne h2 h3, h3 s₀ (List.mem_of_head? h0), ?_⟩
  rw [(totalArgMass_eq_zero_iff _).2 (fun d hd => (List.eq_of_mem_replicate hd))]
  exact Nat.zero_le _

/-- A Hecke chain with all arguments `0`, from an invariant state, is an old-VM chain. -/
theorem HeckeChain.toSteps {S : VMSpec n} {P : HeckePolicy n} :
    ∀ {args : List (HeckeArg n)} {tr : List (VMState n)} {a : VMState n},
      HeckeChain S P args tr → (∀ d ∈ args, d = 0) → tr.head? = some a → VMInvariant S a →
      (∀ i (h : i + 1 < tr.length), step S tr[i] = some tr[i + 1]) ∧ ∀ s' ∈ tr, VMInvariant S s'
  | [], [b], a, _, _, h0, ha => by
    simp only [List.head?_cons, Option.some.injEq] at h0
    subst h0
    exact ⟨fun i hi => by simp at hi, fun s' hs' => by simp at hs'; subst hs'; exact ha⟩
  | d :: ds, b :: t :: rest, a, h, hz, h0, ha => by
    simp only [List.head?_cons, Option.some.injEq] at h0
    subst h0
    have hd : d = 0 := hz d (by simp)
    subst hd
    have hbt : step S b = some t := by rw [← heckeStep_zero S P ha]; exact h.1
    have ht : VMInvariant S t := step_preserves_invariant S hbt
    obtain ⟨ih1, ih2⟩ := HeckeChain.toSteps (tr := t :: rest) h.2
      (fun d hd => hz d (by simp [hd])) rfl ht
    refine ⟨fun i hi => ?_, fun s' hs' => ?_⟩
    · rcases i with _ | i
      · exact hbt
      · exact ih1 i (by simp at hi ⊢; omega)
    · rcases List.mem_cons.1 hs' with rfl | hs'
      · exact ha
      · exact ih2 s' hs'
  | [], [], _, h, _, _, _ | [], _ :: _ :: _, _, h, _, _, _ | _ :: _, [], _, h, _, _, _
  | _ :: _, [_], _, h, _, _, _ => h.elim

/-- **Budget `0` is the conserving VM**: a correct Hecke run whose policy has budget `0` is a correct
run of the old VM. -/
theorem HeckeCorrect.toVMCorrect {S : VMSpec n} {P : HeckePolicy n} (hb : P.budget = 0)
    {s₀ s : VMState n} {args : List (HeckeArg n)} {tr : List (VMState n)}
    (h : HeckeCorrect S P s₀ s args tr) : VMCorrect S s₀ s tr := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  have hz := (totalArgMass_eq_zero_iff args).1 (by omega)
  obtain ⟨hs, hi⟩ := h2.toSteps hz h0 h3
  exact ⟨h0, h1, hs, hi⟩

/-! ### The checker -/

/-- `Bool` check that `t` is the Hecke successor of `s` with argument `d`. -/
def checkHeckeStep (S : VMSpec n) (P : HeckePolicy n) (d : HeckeArg n) (s t : VMState n) : Bool :=
  match heckeStep S P d s with
  | some t' => stateBEq t' t
  | none => false

theorem checkHeckeStep_iff (S : VMSpec n) (P : HeckePolicy n) (d : HeckeArg n) (s t : VMState n) :
    checkHeckeStep S P d s t = true ↔ heckeStep S P d s = some t := by
  unfold checkHeckeStep
  split <;> simp_all [stateBEq_iff]

/-- `Bool` check of a Hecke chain. -/
def checkHeckeChain (S : VMSpec n) (P : HeckePolicy n) :
    List (HeckeArg n) → List (VMState n) → Bool
  | [], [_] => true
  | d :: ds, s :: t :: rest => checkHeckeStep S P d s t && checkHeckeChain S P ds (t :: rest)
  | _, _ => false

theorem checkHeckeChain_iff (S : VMSpec n) (P : HeckePolicy n) :
    ∀ (args : List (HeckeArg n)) (tr : List (VMState n)),
      checkHeckeChain S P args tr = true ↔ HeckeChain S P args tr
  | [], [] | [], [_] | [], _ :: _ :: _ | _ :: _, [] | _ :: _, [_] => by
    simp [checkHeckeChain, HeckeChain]
  | d :: ds, s :: t :: rest => by
    simp only [checkHeckeChain, HeckeChain, Bool.and_eq_true, checkHeckeStep_iff,
      checkHeckeChain_iff S P ds (t :: rest)]

/-- The Hecke trace checker. -/
def checkHeckeTrace (S : VMSpec n) (P : HeckePolicy n) (s₀ s : VMState n)
    (args : List (HeckeArg n)) (tr : List (VMState n)) : Bool :=
  (match tr.head? with | some a => stateBEq a s₀ | none => false) &&
  (match tr.getLast? with | some a => stateBEq a s | none => false) &&
  checkHeckeChain S P args tr && checkVMInvariant S s₀ && decide (totalArgMass args ≤ P.budget)

/-- **Hecke trace checker soundness.** -/
theorem checkHeckeTrace_sound (S : VMSpec n) (P : HeckePolicy n) (s₀ s : VMState n)
    (args : List (HeckeArg n)) (tr : List (VMState n))
    (h : checkHeckeTrace S P s₀ s args tr = true) : HeckeCorrect S P s₀ s args tr := by
  simp only [checkHeckeTrace, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := h
  refine ⟨?_, ?_, (checkHeckeChain_iff S P args tr).1 h2, checkVMInvariant_sound S s₀ h3, h4⟩
  · revert h0; cases tr.head? <;> simp [stateBEq_iff]
  · revert h1; cases tr.getLast? <;> simp [stateBEq_iff]

/-- Kernel evidence for a Hecke run from a closed proof that the checker accepts it. -/
def heckeTraceEvidence (S : VMSpec n) (P : HeckePolicy n) (s₀ s : VMState n)
    (args : List (HeckeArg n)) (tr : List (VMState n))
    (h : checkHeckeTrace S P s₀ s args tr = true) (claim : VerificationClaim) :
    Evidence (HeckeCorrect S P s₀ s args tr) :=
  .kernel (checkHeckeTrace_sound S P s₀ s args tr h) claim

end Dasein15VM

namespace Dasein15VM

variable {n : ℕ}

/-! ### Running a list of Hecke arguments -/

/-- Run the VM with the given Hecke arguments, one per step, returning the trace
(`none` if some step is rejected). -/
def heckeRun (S : VMSpec n) (P : HeckePolicy n) : List (HeckeArg n) → VMState n →
    Option (List (VMState n))
  | [], s => some [s]
  | d :: ds, s => (heckeStep S P d s).bind fun t => (heckeRun S P ds t).map (s :: ·)

/-- A successful run is a Hecke chain starting at its start state. -/
theorem heckeRun_chain (S : VMSpec n) (P : HeckePolicy n) :
    ∀ (args : List (HeckeArg n)) (s : VMState n) {tr : List (VMState n)},
      heckeRun S P args s = some tr → HeckeChain S P args tr ∧ tr.head? = some s
  | [], s, tr, h => by
    simp only [heckeRun, Option.some.injEq] at h
    subst h; exact ⟨trivial, rfl⟩
  | d :: ds, s, tr, h => by
    simp only [heckeRun, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨t, ht, rest, hr, rfl⟩ := h
    obtain ⟨hc, h0⟩ := heckeRun_chain S P ds t hr
    obtain ⟨u, us, rfl⟩ : ∃ u us, rest = u :: us := by
      cases rest with
      | nil => simp at h0
      | cons u us => exact ⟨u, us, rfl⟩
    simp only [List.head?_cons, Option.some.injEq] at h0
    subst h0
    exact ⟨⟨ht, hc⟩, rfl⟩

/-- Conversely, a Hecke chain from `s` is what `heckeRun` produces from `s`. -/
theorem heckeRun_of_chain (S : VMSpec n) (P : HeckePolicy n) :
    ∀ {args : List (HeckeArg n)} {tr : List (VMState n)} {s : VMState n},
      HeckeChain S P args tr → tr.head? = some s → heckeRun S P args s = some tr
  | [], [b], s, _, h0 => by
    simp only [List.head?_cons, Option.some.injEq] at h0
    subst h0; rfl
  | d :: ds, b :: t :: rest, s, h, h0 => by
    simp only [List.head?_cons, Option.some.injEq] at h0
    subst h0
    simp [heckeRun, h.1, heckeRun_of_chain S P (tr := t :: rest) h.2 rfl]
  | [], [], _, h, _ | [], _ :: _ :: _, _, h, _ | _ :: _, [], _, h, _ | _ :: _, [_], _, h, _ =>
    h.elim

end Dasein15VM
