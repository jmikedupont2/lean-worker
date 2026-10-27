import RequestProject.Dasein15VM.UI.Guidance
import Lean.Data.Json

/-!
# RFC-0002 §7: wire format

VM objects and guidance edges serialize to a JSON value type `JVal` (null, booleans, natural
numbers, strings, arrays, objects).  `JVal.toJson` converts to Lean's `Lean.Json` for printing
(`JVal.render`) and `JVal.ofJson?` converts back from parsed text.

**Roundtrip theorems.**  The class `Wire α` packages an encoder, a decoder and the roundtrip law
`dec (enc a) = some a`.  Instances: `ℕ`, `String`, `Bool`, lists, pairs, `ShapeClass`,
`Assurance`, `MaskKind`, `Observable`, `Mask`, `Comparison`, `VerificationClaim`, `VMState n` and
`VMSpec n`.  Decoding a spec re-validates it: the basis entries must be distinct primes and every
route must move every index (`VMSpec.route_ne`).

**Proofs are never on the wire.**  Proof fields are rebuilt on decoding:

* a trace entry is decoded with `decodeTrace S`, which re-runs `checkVMTrace` and attaches
  `checkVMTrace_sound`; a tampered trace fails the checker and is rejected.  The `assurance`
  field is written from `TraceEntry.assurance` and only `kernelEstablished` is accepted.
  `decodeTrace_encodeTrace`: re-decoding a certified entry gives it back (by
  `checkVMTrace_complete`).
* a VM object decodes to a `PreObject` (everything but `omega`/`maskHolds`);
  `PreObject.attach P omega h` re-attaches a **user-supplied** `Mask.Holds` hypothesis, and
  `PreObject.attachObserved?` derives it — only for `witnessedSubset` masks whose orders are
  observed on the object's own certified traces.  `decodeObject_encodeObject` and
  `attach_toPre` give the roundtrip; `attachObserved?_mkVMObject` gives the hypothesis-free
  roundtrip for objects built by `mkVMObject`.
* a guidance edge decodes against its two endpoint objects, re-running `compare`
  (`decodeEdge_encodeEdge`).

Digests and references (`provenance`, `holdsRef`) are strings: pointers, never evidence.
-/

namespace Dasein15VM.UI

open SpectrumVM

/-! ### JSON values -/

/-- JSON values with natural-number literals. -/
inductive JVal
  | null
  | bool (b : Bool)
  | num (n : ℕ)
  | str (s : String)
  | arr (l : List JVal)
  | obj (kvs : List (String × JVal))
  deriving Repr, Inhabited

/-- Object field lookup. -/
def JVal.get? : JVal → String → Option JVal
  | .obj kvs, k => kvs.lookup k
  | _, _ => none

/-- Encoder/decoder pair with the roundtrip law. -/
class Wire (α : Type) where
  enc : α → JVal
  dec : JVal → Option α
  dec_enc : ∀ a, dec (enc a) = some a

attribute [simp] Wire.dec_enc

export Wire (enc dec)

/-- Decode an object field. -/
def JVal.field {β : Type} [Wire β] (j : JVal) (k : String) : Option β := (j.get? k).bind dec

theorem mapM_map_some {α β : Type} (f : β → Option α) (g : α → β) (hfg : ∀ a, f (g a) = some a) :
    ∀ l : List α, (l.map g).mapM f = some l
  | [] => rfl
  | a :: l => by simp [List.mapM_cons, hfg, mapM_map_some f g hfg l]

theorem mapM_comp_some {α β : Type} (f : β → Option α) (g : α → β) (hfg : ∀ a, f (g a) = some a) :
    ∀ l : List α, l.mapM (f ∘ g) = some l
  | [] => rfl
  | a :: l => by simp [List.mapM_cons, hfg, mapM_comp_some f g hfg l]

instance : Wire ℕ where
  enc := .num
  dec | .num n => some n | _ => none
  dec_enc _ := rfl

instance : Wire String where
  enc := .str
  dec | .str s => some s | _ => none
  dec_enc _ := rfl

@[simp] theorem dec_str (s : String) : (dec (JVal.str s) : Option String) = some s := rfl

instance : Wire Bool where
  enc := .bool
  dec | .bool b => some b | _ => none
  dec_enc _ := rfl

instance {α : Type} [Wire α] : Wire (List α) where
  enc l := .arr (l.map enc)
  dec | .arr l => l.mapM dec | _ => none
  dec_enc l := mapM_map_some _ _ Wire.dec_enc l

instance {α β : Type} [Wire α] [Wire β] : Wire (α × β) where
  enc p := .arr [enc p.1, enc p.2]
  dec | .arr [x, y] => do let a ← dec x; let b ← dec y; pure (a, b) | _ => none
  dec_enc p := by simp

/-! ### Enumerations -/

/-- Shape classes are numbered Earth 0, Spoke 1, Hub 2, Clock 3. -/
def clsIndex : ShapeClass → ℕ
  | .Earth => 0 | .Spoke => 1 | .Hub => 2 | .Clock => 3

def clsOfIndex? : ℕ → Option ShapeClass
  | 0 => some .Earth | 1 => some .Spoke | 2 => some .Hub | 3 => some .Clock | _ => none

instance : Wire ShapeClass where
  enc e := .num (clsIndex e)
  dec | .num k => clsOfIndex? k | _ => none
  dec_enc e := by cases e <;> rfl

/-- All four classes, in index order. -/
def allClasses : List ShapeClass := [.Earth, .Spoke, .Hub, .Clock]

theorem mem_allClasses (e : ShapeClass) : e ∈ allClasses := by cases e <;> simp [allClasses]

def assuranceName : Assurance → String
  | .observed => "observed"
  | .external => "external"
  | .externalExecution => "externalExecution"
  | .soundCheckerExecution => "soundCheckerExecution"
  | .kernelEstablished => "kernelEstablished"

def assuranceOfName? (s : String) : Option Assurance :=
  if s = "observed" then some .observed
  else if s = "external" then some .external
  else if s = "externalExecution" then some .externalExecution
  else if s = "soundCheckerExecution" then some .soundCheckerExecution
  else if s = "kernelEstablished" then some .kernelEstablished
  else none

instance : Wire Assurance where
  enc a := .str (assuranceName a)
  dec | .str s => assuranceOfName? s | _ => none
  dec_enc a := by cases a <;> simp [assuranceName, assuranceOfName?]

def maskKindName : MaskKind → String
  | .exact => "exact"
  | .witnessedSubset => "witnessedSubset"
  | .outerBound => "outerBound"

def maskKindOfName? (s : String) : Option MaskKind :=
  if s = "exact" then some .exact
  else if s = "witnessedSubset" then some .witnessedSubset
  else if s = "outerBound" then some .outerBound
  else none

instance : Wire MaskKind where
  enc k := .str (maskKindName k)
  dec | .str s => maskKindOfName? s | _ => none
  dec_enc k := by cases k <;> simp [maskKindName, maskKindOfName?]

instance : Wire Observable where
  enc
    | .mass => .str "mass"
    | .dominantMass => .str "dominantMass"
    | .classMass e => .obj [("classMass", enc e)]
  dec j := match j with
    | .str s => if s = "mass" then some .mass else if s = "dominantMass" then some .dominantMass
        else none
    | j => (j.field "classMass").map Observable.classMass
  dec_enc o := by cases o <;> simp [JVal.field, JVal.get?, List.lookup]

/-! ### Records -/

instance : Wire Mask where
  enc M := .obj [("orders", enc M.orders), ("kind", enc M.kind), ("provenance", enc M.provenance)]
  dec j := do
    let o ← j.field "orders"
    let k ← j.field "kind"
    let p ← j.field "provenance"
    pure ⟨o, k, p⟩
  dec_enc M := by simp [JVal.field, JVal.get?, List.lookup]

instance : Wire Comparison where
  enc
    | .contained ps => .obj [("kind", .str "contained"), ("pairs", enc ps)]
    | .notContained a => .obj [("kind", .str "notContained"), ("witness", enc a)]
    | .unknown us => .obj [("kind", .str "unknown"), ("unresolved", enc us)]
  dec j := do
    let k : String ← j.field "kind"
    if k = "contained" then Comparison.contained <$> j.field "pairs"
    else if k = "notContained" then Comparison.notContained <$> j.field "witness"
    else if k = "unknown" then Comparison.unknown <$> j.field "unresolved"
    else none
  dec_enc c := by cases c <;> simp [JVal.field, JVal.get?, List.lookup]

instance : Wire VerificationClaim where
  enc c := .obj [("propositionDigest", enc c.propositionDigest),
    ("certificateDigest", enc c.certificateDigest), ("verifierDigest", enc c.verifierDigest)]
  dec j := do
    let a ← j.field "propositionDigest"
    let b ← j.field "certificateDigest"
    let c ← j.field "verifierDigest"
    pure ⟨a, b, c⟩
  dec_enc c := by simp [JVal.field, JVal.get?, List.lookup]

variable {n m : ℕ}

theorem getD_ofFn {α : Type} (f : Fin n → α) (i : Fin n) (d : α) :
    (List.ofFn f).getD i d = f i := by
  simp [List.getD_eq_getElem?_getD]

/-- Rebuild a function on `Fin n` from a list. -/
def listFun {α : Type} (l : List α) (d : α) : Fin n → α := fun i => l.getD i d

theorem listFun_ofFn {α : Type} (f : Fin n → α) (d : α) : listFun (List.ofFn f) d = f :=
  funext fun i => getD_ofFn f i d

instance : Wire (VMState n) where
  enc s := .obj [("config", enc s.config), ("steps", enc s.steps),
    ("shape", enc (List.ofFn s.shape)), ("cls", enc s.cls)]
  dec j := do
    let c ← j.field "config"
    let k ← j.field "steps"
    let l : List ℕ ← j.field "shape"
    let e ← j.field "cls"
    if l.length = n then some ⟨c, k, listFun l 0, e⟩ else none
  dec_enc s := by simp [JVal.field, JVal.get?, List.lookup, listFun_ofFn]

/-! ### Specs -/

/-- Rebuild a route table from its rows (out-of-range entries fall back to the identity, which
the validation `route_ne` then rejects). -/
def routeOfRows (rows : List (List ℕ)) : ShapeClass → Fin n → Fin n := fun e i =>
  let k := (rows.getD (clsIndex e) []).getD i 0
  if h : k < n then ⟨k, h⟩ else i

/-- Rows of a route table, in class-index order. -/
def routeRows (r : ShapeClass → Fin n → Fin n) : List (List ℕ) :=
  allClasses.map fun e => List.ofFn fun i => (r e i : ℕ)

theorem routeOfRows_routeRows (r : ShapeClass → Fin n → Fin n) :
    routeOfRows (routeRows r) = r := by
  funext e i
  cases e <;> simp [routeOfRows, routeRows, allClasses, clsIndex, List.getD_eq_getElem?_getD]

/-- Validating constructor of a spec from list data. -/
def specOfLists? (bl : List ℕ) (al : List ShapeClass) (rows : List (List ℕ)) (mass : ℕ) :
    Option (VMSpec n) :=
  if h : bl.length = n ∧ al.length = n ∧ (∀ i : Fin n, (listFun bl 0 i).Prime) ∧
      Function.Injective (listFun (n := n) bl 0) ∧
      (∀ e ∈ allClasses, ∀ i : Fin n, routeOfRows rows e i ≠ i) then
    some { basis := ⟨listFun bl 0, h.2.2.1, h.2.2.2.1⟩
           assign := listFun al .Earth
           route := routeOfRows rows
           route_ne := fun e i => h.2.2.2.2 e (mem_allClasses e) i
           mass := mass }
  else none

theorem specOfLists?_self (S : VMSpec n) :
    specOfLists? (List.ofFn S.basis.p) (List.ofFn S.assign) (routeRows S.route) S.mass =
      some S := by
  unfold specOfLists?
  rw [dif_pos]
  · obtain ⟨⟨p, hp, hi⟩, a, r, hr, ms⟩ := S
    simp only [Option.some.injEq]
    congr 1
    · simp only [listFun_ofFn]
    · exact listFun_ofFn a _
    · exact routeOfRows_routeRows r
  · simp only [List.length_ofFn, listFun_ofFn, routeOfRows_routeRows, true_and]
    exact ⟨S.basis.prime, S.basis.injective, fun e _ i => S.route_ne e i⟩

instance : Wire (VMSpec n) where
  enc S := .obj [("n", enc n), ("basis", enc (List.ofFn S.basis.p)),
    ("assign", enc (List.ofFn S.assign)), ("route", enc (routeRows S.route)),
    ("mass", enc S.mass)]
  dec j := do
    let k : ℕ ← j.field "n"
    let bl ← j.field "basis"
    let al ← j.field "assign"
    let rows ← j.field "route"
    let ms ← j.field "mass"
    if k = n then specOfLists? bl al rows ms else none
  dec_enc S := by simp [JVal.field, JVal.get?, List.lookup, specOfLists?_self]

/-! ### Trace entries -/

/-- Encode a certified trace entry.  `assurance` is copied from the entry's evidence. -/
def encodeTrace {S : VMSpec n} (t : TraceEntry S) : JVal :=
  .obj [("name", enc t.name), ("length", enc t.tr.length), ("checker", .str "checkVMTrace"),
    ("assurance", enc t.assurance), ("init", enc t.init), ("final", enc t.final),
    ("states", enc t.tr), ("claim", enc t.claim)]

/-- Decode a trace entry for the spec `S`: the checker is re-run and its soundness theorem
supplies the `VMCorrect` proof. -/
def decodeTrace (S : VMSpec n) (j : JVal) : Option (TraceEntry S) := do
  let name ← j.field "name"
  let len : ℕ ← j.field "length"
  let a : Assurance ← j.field "assurance"
  let init ← j.field "init"
  let final ← j.field "final"
  let tr : List (VMState n) ← j.field "states"
  let claim ← j.field "claim"
  if a = .kernelEstablished ∧ len = tr.length then
    TraceEntry.ofCheck? S name init final tr claim
  else none

/-- A decoded trace entry is certified: its `VMCorrect` proof is the checker's soundness. -/
theorem decodeTrace_correct {S : VMSpec n} {j : JVal} {t : TraceEntry S}
    (_h : decodeTrace S j = some t) : VMCorrect S t.init t.final t.tr := t.correct

/-- Decoding fails on any trace that does not pass the checker. -/
theorem decodeTrace_eq_none {S : VMSpec n} {j : JVal} {name : String} {init final : VMState n}
    {tr : List (VMState n)} {claim : VerificationClaim}
    (hj : j.field "name" = some name) (hi : j.field "init" = some init)
    (hf : j.field "final" = some final) (ht : j.field "states" = some tr)
    (hc : j.field "claim" = some claim) (hbad : ¬ VMCorrect S init final tr) :
    decodeTrace S j = none := by
  have hn : TraceEntry.ofCheck? S name init final tr claim = none := by
    cases h : TraceEntry.ofCheck? S name init final tr claim
    · rfl
    · exact absurd ((TraceEntry.ofCheck?_isSome_iff (S := S) name init final tr claim).1
        (by rw [h]; rfl)) hbad
  unfold decodeTrace
  rw [hj, hi, hf, ht, hc]
  rcases (j.field "length" : Option ℕ) with _ | len <;>
    rcases (j.field "assurance" : Option Assurance) with _ | a <;> simp [hn]

/-- **Trace roundtrip.** -/
theorem decodeTrace_encodeTrace {S : VMSpec n} (t : TraceEntry S) :
    decodeTrace S (encodeTrace t) = some t := by
  simp [decodeTrace, encodeTrace, JVal.field, JVal.get?, List.lookup, TraceEntry.ofCheck?_self]

/-! ### VM objects -/

/-- A VM object without its semantic order set and `Mask.Holds` hypothesis: what the wire
determines. -/
structure PreObject (n : ℕ) where
  spec : VMSpec n
  obs : Observable
  traces : List (TraceEntry spec)
  mask : Mask
  holdsRef : String
  provenance : VerificationClaim

/-- Forget `omega` and `maskHolds`. -/
def VMObject.toPre (A : VMObject n) (holdsRef : String) : PreObject n :=
  ⟨A.spec, A.obs, A.traces, A.mask, holdsRef, A.provenance⟩

/-- Attach a user-supplied `Mask.Holds` hypothesis. -/
def PreObject.attach (P : PreObject n) (omega : Set ℕ) (h : P.mask.Holds omega) : VMObject n :=
  ⟨P.spec, P.obs, P.traces, P.mask, omega, h, P.provenance⟩

theorem attach_toPre (A : VMObject n) (holdsRef : String) :
    (A.toPre holdsRef).attach A.omega A.maskHolds = A := rfl

/-- Derive the hypothesis for a `witnessedSubset` mask whose orders are all observed on the
object's own certified traces; then `omega` is the semantic order set `specOrders`. -/
def PreObject.attachObserved? (P : PreObject n) : Option (VMObject n) :=
  if h : P.mask.kind = .witnessedSubset ∧
      ∀ a ∈ P.mask.orders, a ∈ observedOrders P.spec P.obs (allStates P.traces) then
    some (P.attach (specOrders P.spec P.obs) (by
      unfold Mask.Holds
      rw [h.1]
      intro a ha
      exact observedMask_sound (provenance := "") (allStates_invariant P.traces) (h.2 a ha)))
  else none

/-- Objects obtained by `attachObserved?` have `omega = specOrders`. -/
theorem attachObserved?_specScoped {P : PreObject n} {A : VMObject n}
    (h : P.attachObserved? = some A) : A.SpecScoped := by
  unfold PreObject.attachObserved? at h
  split_ifs at h
  cases h; rfl

theorem attachObserved?_mkVMObject (spec : VMSpec n) (obs : Observable)
    (traces : List (TraceEntry spec)) (provenance : VerificationClaim) (holdsRef : String) :
    ((mkVMObject spec obs traces provenance).toPre holdsRef).attachObserved? =
      some (mkVMObject spec obs traces provenance) := by
  unfold PreObject.attachObserved?
  rw [dif_pos ⟨rfl, fun a ha => ha⟩]
  rfl

/-- Encode a VM object.  `holdsRef` names the Lean term proving `maskHolds` (a pointer). -/
def encodeObject (A : VMObject n) (holdsRef : String) : JVal :=
  .obj [("schema", .str "dasein15-vm-object/1"), ("spec", enc A.spec),
    ("observable", enc A.obs), ("traces", .arr (A.traces.map encodeTrace)),
    ("mask", enc A.mask), ("maskHolds", enc holdsRef), ("provenance", enc A.provenance)]

/-- Decode a VM object (up to its `Mask.Holds` hypothesis). -/
def decodeObject (n : ℕ) (j : JVal) : Option (PreObject n) := do
  let schema : String ← j.field "schema"
  let spec : VMSpec n ← j.field "spec"
  let obs ← j.field "observable"
  let traces ← match j.get? "traces" with
    | some (.arr l) => l.mapM (decodeTrace spec)
    | _ => none
  let mask ← j.field "mask"
  let holdsRef ← j.field "maskHolds"
  let provenance ← j.field "provenance"
  if schema = "dasein15-vm-object/1" then some ⟨spec, obs, traces, mask, holdsRef, provenance⟩
  else none

/-- **VM object roundtrip** (up to the hypothesis, which `attach_toPre` restores). -/
theorem decodeObject_encodeObject (A : VMObject n) (holdsRef : String) :
    decodeObject n (encodeObject A holdsRef) = some (A.toPre holdsRef) := by
  simp [decodeObject, encodeObject, JVal.field, JVal.get?, List.lookup,
    mapM_comp_some _ _ decodeTrace_encodeTrace, VMObject.toPre]

/-- **Hypothesis-free roundtrip** for objects with observed masks. -/
theorem roundtrip_mkVMObject (spec : VMSpec n) (obs : Observable)
    (traces : List (TraceEntry spec)) (provenance : VerificationClaim) (holdsRef : String) :
    (decodeObject n (encodeObject (mkVMObject spec obs traces provenance) holdsRef)).bind
        PreObject.attachObserved? = some (mkVMObject spec obs traces provenance) := by
  rw [decodeObject_encodeObject, Option.bind_some, attachObserved?_mkVMObject]

/-! ### Guidance edges -/

/-- Encode a guidance edge. -/
def encodeEdge {A : VMObject n} {B : VMObject m} (e : GuidanceEdge A B)
    (holdsA holdsB : String) : JVal :=
  .obj [("schema", .str "dasein15-guidance-edge/1"),
    ("source", enc A.provenance.propositionDigest),
    ("target", enc B.provenance.propositionDigest),
    ("comparison", enc e.comparison), ("soundness", enc e.comparison.soundnessName),
    ("hypotheses", .obj [("maskHoldsSource", enc holdsA), ("maskHoldsTarget", enc holdsB)])]

/-- Decode a guidance edge against its endpoints: `compare` is re-run. -/
def decodeEdge (A : VMObject n) (B : VMObject m) (j : JVal) : Option (GuidanceEdge A B) := do
  let schema : String ← j.field "schema"
  let src : String ← j.field "source"
  let tgt : String ← j.field "target"
  let c : Comparison ← j.field "comparison"
  if schema = "dasein15-guidance-edge/1" ∧ src = A.provenance.propositionDigest ∧
      tgt = B.provenance.propositionDigest then
    if h : c = compare A.mask B.mask then some ⟨c, h⟩ else none
  else none

/-- **Guidance edge roundtrip.** -/
theorem decodeEdge_encodeEdge {A : VMObject n} {B : VMObject m} (e : GuidanceEdge A B)
    (holdsA holdsB : String) : decodeEdge A B (encodeEdge e holdsA holdsB) = some e := by
  obtain ⟨c, hc⟩ := e
  subst hc
  simp [decodeEdge, encodeEdge, JVal.field, JVal.get?, List.lookup]

/-- A decoded edge's verdict is sound (it is the recomputed `compare`). -/
theorem decodeEdge_sound {A : VMObject n} {B : VMObject m} {j : JVal} {e : GuidanceEdge A B}
    (_h : decodeEdge A B j = some e) (hdown : PosDownset B.omega) :
    Verdict e.comparison A.omega B.omega := e.sound hdown

/-! ### Text -/

/-- Convert to `Lean.Json`. -/
def JVal.toJson : JVal → Lean.Json
  | .null => .null
  | .bool b => .bool b
  | .num k => .num (Lean.JsonNumber.fromNat k)
  | .str s => .str s
  | .arr l => .arr (l.attach.map fun ⟨x, _⟩ => x.toJson).toArray
  | .obj kvs => Lean.Json.mkObj (kvs.attach.map fun ⟨p, _⟩ => (p.1, p.2.toJson))
decreasing_by
  · simp_wf; have := List.sizeOf_lt_of_mem ‹x ∈ l›; omega
  · simp_wf
    have := List.sizeOf_lt_of_mem ‹p ∈ kvs›
    cases p; simp at this ⊢; omega

/-- Compact JSON text. -/
def JVal.render (j : JVal) : String := j.toJson.compress

/-- Convert from `Lean.Json` (natural-number literals only). -/
partial def JVal.ofJson? : Lean.Json → Option JVal
  | .null => some .null
  | .bool b => some (.bool b)
  | .num x => if x.exponent = 0 ∧ 0 ≤ x.mantissa then some (.num x.mantissa.toNat) else none
  | .str s => some (.str s)
  | .arr a => (a.toList.mapM JVal.ofJson?).map JVal.arr
  | .obj kvs => (kvs.toList.mapM fun (p : String × Lean.Json) => (JVal.ofJson? p.2).map (p.1, ·)).map JVal.obj

/-- Parse JSON text. -/
def JVal.parse? (s : String) : Option JVal :=
  match Lean.Json.parse s with
  | .ok j => JVal.ofJson? j
  | .error _ => none

end Dasein15VM.UI
