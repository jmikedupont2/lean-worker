import RequestProject.Dasein15VM.VM
import RequestProject.SpectrumVM.Comparison

/-!
# RFC-0002 §6: masks derived from certified traces

The RFC's formula `orderOf (godel A.spec.basis s.shape)` is degenerate: in the multiplicative
monoid `ℕ` only `1` has finite order, so it would send every state of positive mass to `0`
(`orderOf_godel_eq_zero`).  The "order" read off a state is therefore a selectable
*observable* (`Observable`), serialized by name.

* `Observable.eval S o s`: the value of the observable `o` on the state `s`.
* `specOrders S o`: the semantic order set `ω` of a spec — the values of `o` on all invariant
  states.  `specOrders_eq_traceOrders` shows that this is exactly the set of values of `o` along
  all certified (`VMCorrect`) traces of `S`.
* `observedMask S o states prov`: the deduplicated values of `o` on a list of states, with kind
  `witnessedSubset` (`observedMask_kind`: the kind is never upgraded).
* `observedMask_sound` / `observedMask_holds`: if every listed state lies on a certified trace,
  every observed order belongs to `specOrders S o`, i.e. `(observedMask …).Holds (specOrders S o)`
  (the analogue of `ObservedSpectrum.subset_omega`).
-/

namespace Dasein15VM.UI

open SpectrumVM

variable {n : ℕ}

/-- The literal formula of the RFC: in the monoid `ℕ` the Gödel number of a shape of positive
mass has infinite order, so `orderOf` returns `0`. -/
theorem orderOf_godel_eq_zero (B : PrimeBasis n) (v : PrimeShape n) (hv : 0 < mass v) :
    orderOf (godel B v) = 0 := by
  rw [orderOf_eq_zero_iff']
  intro k hk hpow
  have h1 : godel B v = 1 := (pow_eq_one_iff.1 hpow).resolve_right hk.ne'
  rw [mass_eq_sum] at hv
  obtain ⟨i, -, hi⟩ := Finset.exists_lt_of_sum_lt (s := Finset.univ) (f := fun _ => 0)
    (by simpa using hv)
  have hd := (dvd_godel_iff B v i).2 hi
  rw [h1, Nat.dvd_one] at hd
  exact (B.prime i).one_lt.ne' hd

/-- Observables: the "order" read off a VM state. -/
inductive Observable
  /-- Total mass of the shape. -/
  | mass
  /-- Mass of the state's (dominant) class. -/
  | dominantMass
  /-- Mass carried by a fixed class. -/
  | classMass (e : ShapeClass)
  deriving DecidableEq, Repr

/-- Value of an observable on a state. -/
def Observable.eval (S : VMSpec n) : Observable → VMState n → ℕ
  | .mass, s => Dasein15VM.mass s.shape
  | .dominantMass, s => Dasein15VM.classMass S.assign s.cls s.shape
  | .classMass e, s => Dasein15VM.classMass S.assign e s.shape

/-- **The semantic order set of a spec**: values of the observable on all invariant states. -/
def specOrders (S : VMSpec n) (o : Observable) : Set ℕ :=
  {m | ∃ x, VMInvariant S x ∧ o.eval S x = m}

/-- Values of the observable along certified traces. -/
def traceOrders (S : VMSpec n) (o : Observable) : Set ℕ :=
  {m | ∃ s₀ s tr, VMCorrect S s₀ s tr ∧ ∃ x ∈ tr, o.eval S x = m}

/-- An invariant state is a certified one-state trace. -/
theorem VMCorrect.singleton {S : VMSpec n} {x : VMState n} (h : VMInvariant S x) :
    VMCorrect S x x [x] :=
  ⟨rfl, rfl, fun i hi => by simp at hi, fun y hy => by simp at hy; exact hy ▸ h⟩

/-- The order set of a spec is exactly the set of orders along its certified traces. -/
theorem specOrders_eq_traceOrders (S : VMSpec n) (o : Observable) :
    specOrders S o = traceOrders S o := by
  ext m
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, x, [x], VMCorrect.singleton hx, x, by simp, rfl⟩
  · rintro ⟨s₀, s, tr, h, x, hx, rfl⟩
    exact ⟨x, h.2.2.2 x hx, rfl⟩

/-- Observed orders of a list of states (deduplicated). -/
def observedOrders (S : VMSpec n) (o : Observable) (states : List (VMState n)) : List ℕ :=
  (states.map (o.eval S)).dedup

/-- **The observed mask.**  Its kind is `witnessedSubset`, never `exact`. -/
def observedMask (S : VMSpec n) (o : Observable) (states : List (VMState n))
    (provenance : String) : Mask :=
  ⟨observedOrders S o states, .witnessedSubset, provenance⟩

/-- Never upgrade: an observed mask is a witnessed subset. -/
@[simp] theorem observedMask_kind (S : VMSpec n) (o : Observable) (states : List (VMState n))
    (provenance : String) : (observedMask S o states provenance).kind = .witnessedSubset := rfl

theorem mem_observedOrders {S : VMSpec n} {o : Observable} {states : List (VMState n)} {m : ℕ} :
    m ∈ observedOrders S o states ↔ ∃ x ∈ states, o.eval S x = m := by
  simp [observedOrders]

/-- **Soundness of the observed mask**: if every listed state is invariant (for instance, lies on
a certified trace), every observed order lies in the semantic order set. -/
theorem observedMask_sound {S : VMSpec n} {o : Observable} {states : List (VMState n)}
    {provenance : String} (hinv : ∀ x ∈ states, VMInvariant S x) {m : ℕ}
    (hm : m ∈ (observedMask S o states provenance).orders) : m ∈ specOrders S o := by
  obtain ⟨x, hx, rfl⟩ := mem_observedOrders.1 hm
  exact ⟨x, hinv x hx, rfl⟩

/-- Soundness for the states of one certified trace. -/
theorem observedMask_sound_of_trace {S : VMSpec n} {o : Observable} {s₀ s : VMState n}
    {tr : List (VMState n)} {provenance : String} (h : VMCorrect S s₀ s tr) {m : ℕ}
    (hm : m ∈ (observedMask S o tr provenance).orders) : m ∈ traceOrders S o :=
  specOrders_eq_traceOrders S o ▸ observedMask_sound h.2.2.2 hm

/-- The observed mask describes the semantic order set as a witnessed subset. -/
theorem observedMask_holds {S : VMSpec n} {o : Observable} {states : List (VMState n)}
    {provenance : String} (hinv : ∀ x ∈ states, VMInvariant S x) :
    (observedMask S o states provenance).Holds (specOrders S o) :=
  fun _ hm => observedMask_sound hinv hm

end Dasein15VM.UI
