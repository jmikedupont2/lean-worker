import RequestProject.Analyzer

/-!
# v2 labels and v3 spec-extraction proposals

## v2: per-declaration labels

Every edge `D → A` to a *definition* `A` is classified by `classifyEdge`
(`stmt` / `stmtUnfold` / `proofOnly` / `unfold`) and then given a verdict:

* `stmtUnfold` with `D` in the same module as `A` – **fixed** if no proof of `D` from `A`'s
  *other* lemmas exists (checked with the v3 machinery, `api`/`patch-api` strategies only):
  `D` is then part of `A`'s own API (`R(D) = D`), the edge is accepted and `D` stays in
  `A`'s chunk. If such a proof exists the edge is **abstractable** instead;
* `stmtUnfold` from another module, or `unfold` – **abstractable**: the proof relies on
  `A`'s definition and should go through a spec of `A` instead (`R(D) ≠ D`);
* `proofOnly` – **reprove**: `A` occurs only in the proof and is not unfolded; the proof
  can be redone through other lemmas without changing anything else;
* `stmt` – nothing to do (interface edge).

A declaration is labelled by its worst edge: `abstractable` > `reprove` > `fixed` > `clean`
(`clean`: only interface edges to definitions).

Edges to theorems are never coupling of this kind (proofs are irrelevant), but a proof edge
to an `@[simp]` lemma is reported as an **attribute edge**: moving that lemma, or its
attribute, can silently change the proof.

## v3: proposals

For an abstractable edge `D → A` a proposal is a new proof of `D`'s *unchanged* statement
that is checked in a scratch environment where `A` is `@[irreducible]`. Strategies, tried
in order (the first that passes is reported):

0. `inline`  – (only if `A` is not in the statement) inline `A`'s body into the proof;
1. `api`     – rewrite with existing lemmas about `A` from `A`'s module, then reuse the
              original proof with `A` inlined;
2. `extract` – extract one new spec lemma, `A`'s defining equation (`∀ xs, A xs = body`,
              proved by `rfl` where `A` is still transparent), rewrite with it, then reuse
              the original proof with `A` inlined;
3. `simp`    – reprove from scratch by `simp` with `A`'s lemmas and the extracted spec.

Proposals are made for proofs only (declarations whose type is a proposition): a new body
for a definition or instance could change definitional behaviour downstream, so abstractable
edges of data declarations are always held back for review.

A proposal is accepted only if the new term passes the transparency-respecting check with
`A` irreducible **and** is accepted by the kernel as a declaration whose type is
syntactically the original statement (the statement-equality gate).
-/

open Lean Meta Elab Tactic

namespace Decouple

/-- Verdict for one edge to a definition. -/
inductive EdgeVerdict where
  | interface | fixed | abstractable | reprove
  deriving Repr, BEq, Inhabited

/-- Per-declaration label, ordered by how much work cutting it loose requires. -/
inductive DeclLabel where
  | clean | fixed | reprove | abstractable
  deriving Repr, BEq, Inhabited, Ord

instance : ToString DeclLabel where
  toString
    | .clean => "clean" | .fixed => "fixed" | .reprove => "reprove"
    | .abstractable => "abstractable"

def DeclLabel.rank : DeclLabel → Nat
  | .clean => 0 | .fixed => 1 | .reprove => 2 | .abstractable => 3

def moduleOf? (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!

/-- Same module (declarations of the current file count as one module). -/
def sameModule (env : Environment) (a b : Name) : Bool :=
  moduleOf? env a == moduleOf? env b

/-- Verdict of an edge, given its class. -/
def verdict (env : Environment) (decl dep : Name) : EdgeClass → EdgeVerdict
  | .stmtUnfold => if sameModule env decl dep then .fixed else .abstractable
  | .unfold => .abstractable
  | .proofOnly => .reprove
  | _ => .interface

/-- Definitions whose edges are probed. Structure projections (including parent-structure
projections such as `Lattice.toSemilatticeSup`) are excluded: they are part of the
statement-level interface of their structure and cannot be abstracted further. -/
def isProbeTarget (env : Environment) (t : Name) : Bool :=
  match env.find? t with
  | some (.defnInfo _) => !env.isProjectionFn t && !isParentProjection
  | _ => false
where
  /-- non-subobject parent projections (e.g. `SemilatticeInf.toMin`) are ordinary
  definitions, recorded in the parent info of their structure -/
  isParentProjection : Bool :=
    match t with
    | .str s _ => isStructure env s && (getStructureParentInfo env s).any (·.projFn == t)
    | _ => false

/-- The v2 result for one declaration. -/
structure DeclReport where
  name     : Name
  label    : DeclLabel
  edges    : Array (Name × EdgeVerdict)   -- edges to definitions with a non-interface verdict
  simpUses : Array Name                   -- attribute edges: `@[simp]` lemmas used in the proof
  deriving Inhabited

/-- Is `n` a theorem tagged `@[simp]`? -/
def isSimpLemma (n : Name) : MetaM Bool := do
  try return (← getSimpTheorems).isLemma (.decl n) catch _ => return false

/-! ## v3 -/

/-- Replace every occurrence of the constant `dep` by its (universe-instantiated) value. -/
def inlineConst (dep : Name) (e : Expr) : MetaM Expr := do
  let some ci := (← getEnv).find? dep | return e
  let some v := ci.value? | return e
  let e' := e.replace fun
    | .const n ls => if n == dep then some (v.instantiateLevelParams ci.levelParams ls) else none
    | _ => none
  Core.betaReduce e'

/-- Add the defining equation of `dep` as a theorem `dep.decouple_spec`, proved by `rfl`
while `dep` is still transparent. Returns its name. -/
def extractSpec (dep : Name) : MetaM (Option Name) := do
  let env ← getEnv
  let some ci := env.find? dep | return none
  let some v := ci.value? | return none
  let specName := dep ++ `decouple_spec
  if env.contains specName then return some specName
  let us := ci.levelParams.map mkLevelParam
  let (ty, pf) ← lambdaTelescope v fun xs body => do
    let lhs := mkAppN (.const dep us) xs
    let eq ← mkEq lhs body
    return (← mkForallFVars xs eq, ← mkLambdaFVars xs (← mkEqRefl lhs))
  try
    addDecl (.thmDecl { name := specName, levelParams := ci.levelParams, type := ty, value := pf })
    return some specName
  catch _ => return none

/-- Does `a` come strictly before `b` in source order? (Only meaningful within one module;
across modules the import order already guarantees acyclicity.) -/
def declaredBefore (a b : Name) : MetaM Bool := do
  let env ← getEnv
  unless sameModule env a b do return true
  let some ra ← findDeclarationRanges? a | return false
  let some rb ← findDeclarationRanges? b | return false
  return ra.range.pos.line < rb.range.pos.line

/-- Theorems in `dep`'s module that mention `dep` in their statement and are declared
before `decl` (so a proposal can never create a cycle, even jointly with other proposals). -/
def apiLemmas (decl dep : Name) (limit := 40) : MetaM (Array Name) := do
  let env ← getEnv
  -- constants of `dep`'s module; for the current file, the locally added constants
  let names := match env.getModuleIdxFor? dep with
    | some idx => env.header.moduleData[idx.toNat]!.constNames
    | none => (env.constants.map₂.toList.map Prod.fst).toArray
  let mut out := #[]
  for n in names do
    if out.size ≥ limit then break
    if n == decl || n.isInternal || collapse n != n then continue
    let some (.thmInfo ti) := env.find? n | continue
    unless ti.type.getUsedConstants.contains dep do continue
    unless ← declaredBefore n decl do continue
    out := out.push n
  return out

/-- Run `x` with a heartbeat budget, turning *every* failure (including runtime exceptions
such as deep recursion or heartbeat exhaustion) into `none`. -/
def guarded {α} (x : MetaM (Option α)) (heartbeats : Nat := 400000) : MetaM (Option α) :=
  controlAt CoreM fun runInBase =>
    Core.tryCatchRuntimeEx
      (withTheReader Core.Context (fun c => { c with maxHeartbeats := heartbeats * 1000 }) <|
        withCurrHeartbeats (runInBase x))
      (fun _ => runInBase (pure none))

/-- Run a tactic (given as source text) on a fresh goal; return the remaining goals. -/
def runTacticText (goal : MVarId) (src : String) : MetaM (Option (List MVarId)) := do
  let env ← getEnv
  let .ok stx := Parser.runParserCategory env `tactic src | return none
  let msgs := (← getThe Core.State).messages
  try
    guarded <| withOptions (·.setBool `linter.unusedSimpArgs false) do
      return some (← Term.TermElabM.run' (Tactic.run goal (evalTactic stx)))
  catch _ => return none
  finally
    -- tactic diagnostics from scratch attempts are not part of the report
    modifyThe Core.State fun st => { st with messages := msgs }

def simpArgs (ls : Array Name) : String :=
  ", ".intercalate (ls.map fun n => toString (mkIdent n).getId).toList

/-- A verified proposal for an abstractable edge. -/
structure Proposal where
  decl     : Name
  dep      : Name
  strategy : String
  lemmas   : Array Name
  /-- the new proof of `decl`'s unchanged statement (checked with `dep` irreducible) -/
  proof    : Expr
  deriving Inhabited

/-- Kernel gate: the new proof is accepted by the kernel, synchronously, as a declaration with
*the original type* (a theorem for propositions, a definition otherwise). Nothing is added
to the environment. -/
def kernelGate (ci : ConstantInfo) (pf : Expr) : MetaM Bool := do
  let nm := ci.name ++ `decouple_proposal
  let decl : Declaration ←
    if ← isProp ci.type then
      pure (.thmDecl { name := nm, levelParams := ci.levelParams, type := ci.type, value := pf })
    else
      pure (.defnDecl (mkDefinitionValEx nm ci.levelParams ci.type pf .opaque .safe [nm]))
  match Kernel.Environment.addDecl (← getEnv).toKernelEnv (← getOptions) decl with
  | .ok _ => return true
  | .error _ => return false

/-- Try one strategy: optionally run `pre` (a rewriting tactic) on the statement, then close
what is left with the original proof with `dep` inlined (or by `pre` alone). The result
must pass the irreducibility check and the kernel gate. Runs with `dep` irreducible. -/
def tryStrategy (ci : ConstantInfo) (dep : Name) (pre : Option String) :
    MetaM (Option Expr) := do
  let some val := ci.value? (allowOpaque := true) | return none
  let val' ← inlineConst dep val
  let root ← mkFreshExprMVar ci.type
  let mut goals := [root.mvarId!]
  if let some t := pre then
    let some gs ← runTacticText root.mvarId! t | return none
    goals := gs
  for g in goals do
    let gt ← g.getType
    let ok ← withTransparency .default <| isDefEq gt (← inferType val')
    unless ok do return none
    g.assign val'
  let pf ← instantiateMVars root
  if pf.hasMVar then return none
  unless ← checksAtDefault ci pf do return none
  return if ← kernelGate ci pf then some pf else none

/-- Prove `lhs = rhs` by rewriting with `lemmas` (then `rfl`), with the current transparency
settings (so with the probed dependency irreducible). -/
def bridgeEq (lemmas : Array Name) (lhs rhs : Expr) : MetaM (Option Expr) := do
  let goal ← mkFreshExprMVar (← mkEq lhs rhs)
  let some gs ← runTacticText goal.mvarId! s!"simp only [{simpArgs lemmas}]" | return none
  for g in gs do
    let some [] ← runTacticText g "rfl" | return none
  let pf ← instantiateMVars goal
  return if pf.hasMVar then none else some pf

/-- Transport `a : ta` to type `d` along `h : ta = d` (`Eq.mp` for proofs, `cast` for data). -/
def transport (h a : Expr) : MetaM Expr := do
  if ← isProp (← inferType a) then mkEqMP h a else mkAppM ``cast #[h, a]

/-- Proof repair: walk the term as the probe's checker does and, at every point where a
conversion fails because `dep` is irreducible, insert a rewrite along an equation proved
from `lemmas`. Returns the patched term and the number of patch points. -/
partial def repair (lemmas : Array Name) (e : Expr) : StateT Nat MetaM Expr := do
  let bridge (a ta d : Expr) : StateT Nat MetaM Expr := do
    if ← isDefEq d ta then return a
    let some h ← bridgeEq lemmas ta d | throwError "repair: cannot bridge {ta} and {d}"
    modify (· + 1)
    transport h a
  match e with
  | .app .. =>
    e.withApp fun f args => do
      let mut f' ← repair lemmas f
      let mut fType ← inferType f'
      let mut done : Array Expr := #[]
      for a in args do
        let a' ← repair lemmas a
        unless (← whnf fType).isForall do
          -- the head needs `dep` unfolded to become a function: transport it
          let fType' ← withTransparency .all <| whnf fType
          let g := mkAppN f' done
          let g' ← bridge g fType fType'
          f' := g'; done := #[]; fType := fType'
        let .forallE _ d b _ ← whnf fType | throwError "repair: not a function type"
        let a'' ← bridge a' (← inferType a') d
        done := done.push a''
        fType := b.instantiate1 a''
      return mkAppN f' done
  | .lam n d b bi =>
    let d' ← repair lemmas d
    withLocalDecl n bi d' fun x => do mkLambdaFVars #[x] (← repair lemmas (b.instantiate1 x))
  | .forallE n d b bi =>
    let d' ← repair lemmas d
    withLocalDecl n bi d' fun x => do mkForallFVars #[x] (← repair lemmas (b.instantiate1 x))
  | .letE _ _ v b _ => repair lemmas (b.instantiate1 v)
  | .mdata _ b => repair lemmas b
  | .proj s i b => return .proj s i (← repair lemmas b)
  | _ => return e

/-- Strategy `patch`: repair the original proof term in place, then bridge its type to the
statement if needed. Returns the number of patch points on success. -/
def tryPatch (ci : ConstantInfo) (lemmas : Array Name) : MetaM (Option (Expr × Nat)) := do
  let some val := ci.value? (allowOpaque := true) | return none
  try
    let (v, k) ← (repair lemmas val).run 0
    let tv ← inferType v
    let (pf, k) ← if ← isDefEq tv ci.type then pure (v, k) else
      match ← bridgeEq lemmas tv ci.type with
      | some h => pure (← transport h v, k + 1)
      | none => return none
    let pf ← instantiateMVars pf
    unless ← checksAtDefault ci pf do return none
    return if ← kernelGate ci pf then some (pf, k) else none
  catch _ => return none

/-- Keep only the lemmas that the accepted proof actually uses (simp auxiliaries included). -/
def usedLemmas (lemmas : Array Name) (pf : Expr) : Array Name :=
  let used := pf.getUsedConstants.map collapse
  lemmas.filter used.contains

/-- Search for a proposal for the edge `decl → dep`, in a scratch environment. -/
def proposeCore (decl dep : Name) (apiOnly := false) : MetaM (Option Proposal) := do
  let saved ← getEnv
  try
    let some ci := (← getEnv).find? decl | return none
    -- only proofs are rewritten: a new body for data could change definitional behaviour
    -- downstream, so such edges are always held back for review
    unless ← isProp ci.type do return none
    let api ← apiLemmas decl dep
    let spec ← extractSpec dep
    setReducibilityStatus dep .irreducible
    let inStmt := ci.type.getUsedConstants.contains dep
    if apiOnly then
      let r ← guarded (tryStrategy ci dep (some s!"simp only [{simpArgs api}]"))
      if let some proof := r then return some { decl, dep, strategy := "api", lemmas := api, proof }
      let r ← guarded (tryPatch ci api)
      if let some (proof, k) := r then
        return some { decl, dep, strategy := s!"patch-api, {k} rewrite point(s)", lemmas := api, proof }
      return none
    let attempts : List (String × Array Name × Option String) :=
      (if inStmt then [] else [("inline", #[], none)]) ++
      (if api.isEmpty then [] else [("api", api, some s!"simp only [{simpArgs api}]")]) ++
      (match spec with
        | some s => [("extract", #[s], some s!"simp only [{simpArgs #[s]}]")]
        | none => []) ++
      [("simp", api ++ spec.toArray, some s!"simp [{simpArgs (api ++ spec.toArray)}]")]
    for (strategy, lemmas, pre) in attempts.take (attempts.length - 1) do
      let env ← getEnv
      let r ← guarded (tryStrategy ci dep pre)
      setEnv env
      if let some proof := r then return some { decl, dep, strategy, lemmas, proof }
    -- patch the proof in place, with the existing API first, then with the extracted spec
    for (strategy, lemmas) in [("patch-api", api), ("patch-extract", spec.toArray)] do
      if lemmas.isEmpty then continue
      let env ← getEnv
      let r ← guarded (tryPatch ci lemmas)
      setEnv env
      if let some (proof, k) := r then
        return some { decl, dep, strategy := s!"{strategy}, {k} rewrite point(s)", lemmas, proof }
    for (strategy, lemmas, pre) in attempts.drop (attempts.length - 1) do
      let env ← getEnv
      let r ← guarded (tryStrategy ci dep pre)
      setEnv env
      if let some proof := r then return some { decl, dep, strategy, lemmas, proof }
    return none
  finally
    setEnv saved

/-- `proposeCore`, reporting only the lemmas the accepted proof actually uses. -/
def propose (decl dep : Name) (apiOnly := false) : MetaM (Option Proposal) := do
  return (← proposeCore decl dep apiOnly).map fun p =>
    let used := usedLemmas p.lemmas p.proof
    -- a rewrite step that used no lemma only normalised the goal: the proposal is an inlining
    let strategy := if used.isEmpty && (p.strategy == "api" || p.strategy == "extract")
      then "inline" else p.strategy
    { p with lemmas := used, strategy }

/-- Label one declaration. `targets` restricts which definitions are probed
(e.g. only those inside the analysed subtree); `none` probes all. -/
def labelDecl (d : Name) (targets : Option NameSet := none) :
    MetaM DeclReport := do
  let env ← getEnv
  let fp ← footprint d
  let mut edges := #[]
  let mut label := DeclLabel.clean
  for t in fp.stmt ++ fp.proof do
    if let some ts := targets then unless ts.contains t do continue
    unless isProbeTarget env t do continue
    let mut v := verdict env d t (← classifyEdge d t)
    -- a same-module spec-style edge is a fixed point only if `A`'s other lemmas cannot
    -- replace the unfolding (R(D) = D); otherwise it is abstractable
    if v == .fixed then
      if (← propose d t (apiOnly := true)).isSome then v := .abstractable
    let l : DeclLabel := match v with
      | .fixed => .fixed | .abstractable => .abstractable | .reprove => .reprove
      | .interface => .clean
    if l.rank > label.rank then label := l
    if v != .interface then edges := edges.push (t, v)
  let simpUses ← fp.proof.filterM fun t => do
    let some (.thmInfo _) := env.find? t | return false
    isSimpLemma t
  return { name := d, label, edges, simpUses }

end Decouple
