import Lean

/-!
# Prototype decoupling analyzer (v1 + term-level v2 probe)

Read-only analysis of a set of declarations:

* `stmtDeps`  – constants in the type (the interface),
* `proofDeps` – constants in the value minus the statement footprint (the implementation),
* `instDeps`  – instances used in the value (instance edges),
* compiler-generated names are collapsed into their parent,
* `sccs`      – Tarjan strongly connected components of the stmt+proof graph,
* `unfoldProbe` – a term-level irreducibility probe: mark a dependency `@[irreducible]`
  in a scratch copy of the environment and re-check the *elaborated* value against the
  stated type at default transparency.  A failure is an `unfold` edge.

The probe re-checks the elaborated term rather than re-running tactics, so it finds
defeq reliance that survives in the final term (e.g. `rfl`, `show`, `change`, `decide`)
but not reliance that only affects tactic search (e.g. `simp` finding a different path).
-/

open Lean Meta

namespace Decouple

/-- Name components that indicate a compiler- or elaborator-generated auxiliary. -/
def auxComponents : List String :=
  ["match_", "proof_", "eq_", "_private", "_cstage", "_spec", "_unfold", "eq_def",
   "rec", "recOn", "casesOn", "below", "brecOn", "noConfusion", "noConfusionType",
   "_sunfold", "_closed", "_lambda"]

/-- Is this component an auxiliary marker (e.g. `match_1`, `proof_3`, `eq_2`)? -/
def isAuxComponent (s : String) : Bool :=
  auxComponents.any fun p => s == p || (p.endsWith "_" && s.startsWith p)

/-- Collapse a generated name into the user-facing parent it was generated for. -/
partial def collapse (n : Name) : Name :=
  match n with
  | .str p s => if isAuxComponent s || n.isInternal then collapse p else n
  | .num p _ => collapse p
  | .anonymous => n

/-- Collapse and deduplicate, dropping the declaration itself. -/
def normalize (self : Name) (ns : Array Name) : Array Name :=
  (ns.map collapse).foldl (init := #[]) fun acc m =>
    if m == self || m.isAnonymous || acc.contains m then acc else acc.push m

/-- A typed footprint for one declaration. -/
structure Footprint where
  name  : Name
  stmt  : Array Name
  proof : Array Name
  inst  : Array Name
  simp  : Bool
  deriving Inhabited, Repr

/-- Constants occurring in the value of a constant, if it has one. Theorems included. -/
def valueConsts (ci : ConstantInfo) : Array Name :=
  match ci with
  | .thmInfo v    => v.value.getUsedConstants
  | .defnInfo v   => v.value.getUsedConstants
  | .opaqueInfo v => v.value.getUsedConstants
  | _ => #[]

/-- Compute the typed footprint of a declaration. -/
def footprint (n : Name) : MetaM Footprint := do
  let env ← getEnv
  let some ci := env.find? n | throwError "unknown constant {n}"
  let stmt := normalize n ci.type.getUsedConstants
  -- Recursive definitions are compiled (e.g. via `brecOn`), which can hide calls to
  -- mutually recursive siblings; the smart-unfolding / unsafe auxiliaries keep them.
  let aux := [`_sunfold, `_unsafe_rec].filterMap fun s =>
    (env.find? (n ++ s)).map valueConsts
  let val  := normalize n (aux.foldl (· ++ ·) (valueConsts ci))
  let proof := val.filter (!stmt.contains ·)
  let inst ← val.filterM fun c => return isInstanceCore env c
  let simp ← (do
    let s ← getSimpTheorems
    return s.isLemma (.decl n)) <|> pure false
  return { name := n, stmt, proof, inst, simp }

/-- User-facing declarations whose defining module's name starts with `pre`. -/
def declsInModules (pre : Name) : MetaM (Array Name) := do
  let env ← getEnv
  let mods := env.header.moduleNames
  let mut out := #[]
  for (n, _) in env.constants.map₁.toList do
    if collapse n != n then continue
    let some idx := env.getModuleIdxFor? n | continue
    if pre.isPrefixOf mods[idx.toNat]! then out := out.push n
  return out

/-- Tarjan's SCC algorithm on an adjacency map restricted to `nodes`. -/
partial def sccs (nodes : Array Name) (adj : NameMap (Array Name)) : Array (Array Name) := Id.run do
  let nodeSet : NameSet := nodes.foldl (·.insert ·) {}
  let mut index : NameMap Nat := {}
  let mut low : NameMap Nat := {}
  let mut onStack : NameSet := {}
  let mut stack : Array Name := #[]
  let mut counter := 0
  let mut out : Array (Array Name) := #[]
  -- iterative DFS with explicit work stack of (node, next-child-position)
  for root in nodes do
    if index.contains root then continue
    let mut work : Array (Name × Nat) := #[(root, 0)]
    index := index.insert root counter; low := low.insert root counter; counter := counter + 1
    stack := stack.push root; onStack := onStack.insert root
    while h : work.size > 0 do
      let (v, i) := work[work.size - 1]
      let succs := ((adj.find? v).getD #[]).filter nodeSet.contains
      if hi : i < succs.size then
        work := work.set! (work.size - 1) (v, i + 1)
        let w := succs[i]
        if !index.contains w then
          index := index.insert w counter; low := low.insert w counter; counter := counter + 1
          stack := stack.push w; onStack := onStack.insert w
          work := work.push (w, 0)
        else if onStack.contains w then
          low := low.insert v (min (((low.get? v).getD 0)) (((index.get? w).getD 0)))
      else
        work := work.pop
        if h' : work.size > 0 then
          let (u, _) := work[work.size - 1]
          low := low.insert u (min (((low.get? u).getD 0)) (((low.get? v).getD 0)))
        if ((low.get? v).getD 0) == ((index.get? v).getD 0) then
          let mut comp := #[]
          let mut done := false
          while !done do
            let x := stack.back!
            stack := stack.pop; onStack := onStack.erase x
            comp := comp.push x
            done := x == v
          out := out.push comp
  return out

/-- Result of probing one dependency of a declaration. -/
inductive ProbeResult where
  | ok        -- still checks with the dependency irreducible
  | unfold    -- fails: the elaborated term relies on unfolding the dependency
  | skipped   -- dependency is not a definition, nothing to probe
  deriving Repr, BEq

/-- Type-check a term at the *ambient* transparency (`Meta.check` always uses `.all`,
which would ignore `@[irreducible]`). Function types are still whnf'd at `.all`,
mirroring `Meta.check`, so only argument/expected-type conversions are probed. -/
partial def checkAtAmbient (e : Expr) : MetaM Unit := do
  match e with
  | .app .. =>
    e.withApp fun f args => do
      checkAtAmbient f
      args.forM checkAtAmbient
      let mut fType ← inferType f
      for a in args do
        unless fType.isForall do fType ← withTransparency .all <| whnf fType
        let .forallE _ d b _ := fType | throwError "probe: not a function type"
        unless ← isDefEq d (← inferType a) do
          throwError "probe: argument type mismatch"
        fType := b.instantiate1 a
  | .lam n d b bi | .forallE n d b bi =>
    checkAtAmbient d
    withLocalDecl n bi d fun x => checkAtAmbient (b.instantiate1 x)
  | .letE _ t v b _ =>
    checkAtAmbient t; checkAtAmbient v
    unless ← isDefEq t (← inferType v) do throwError "probe: let type mismatch"
    checkAtAmbient (b.instantiate1 v)
  | .mdata _ b | .proj _ _ b => checkAtAmbient b
  | _ => pure ()

/-- Does the elaborated value of `ci` still check against its type at default transparency? -/
def checksAtDefault (ci : ConstantInfo) (val : Expr) (heartbeats : Nat := 200000) :
    MetaM Bool :=
  -- every failure counts as "does not check", including runtime exceptions (heartbeat
  -- exhaustion, deep recursion); each check gets its own heartbeat budget
  controlAt CoreM fun runInBase =>
    Core.tryCatchRuntimeEx
      (withTheReader Core.Context (fun c => { c with maxHeartbeats := heartbeats * 1000 }) <|
        withCurrHeartbeats <| runInBase <| withTransparency .default do
          try
            checkAtAmbient val
            isDefEq (← inferType val) ci.type
          catch _ => pure false)
      (fun _ => runInBase (pure false))

/-- Term-level irreducibility probe for `dep` inside the value of `decl`.
A baseline check is run first: if the term does not check at default transparency even
before `dep` is made irreducible, the probe is inconclusive and returns `.skipped`. -/
def probe (decl dep : Name) : MetaM ProbeResult := do
  let env ← getEnv
  let some ci := env.find? decl | throwError "unknown constant {decl}"
  let some (.defnInfo _) := env.find? dep | return .skipped
  let some val := ci.value? (allowOpaque := true) | return .skipped
  unless ← checksAtDefault ci val do return .skipped
  let saved ← getEnv
  try
    setReducibilityStatus dep .irreducible
    return if ← checksAtDefault ci val then .ok else .unfold
  finally
    setEnv saved

/-- All unfold edges of `decl` (dependencies whose irreducibility breaks it). -/
def unfoldEdges (decl : Name) : MetaM (Array Name) := do
  let fp ← footprint decl
  (fp.stmt ++ fp.proof).filterM fun d => return (← probe decl d) == .unfold

/-- Decision-table classification for an edge `decl → dep`. -/
inductive EdgeClass where
  | none        -- no edge
  | stmt        -- interface edge: legitimate if it points downward
  | stmtUnfold  -- interface edge whose proof also unfolds `dep` (e.g. `rfl`)
  | proofOnly   -- implementation edge, replaceable by API lemmas (reprove)
  | unfold      -- proof relies on unfolding `dep`: extract a spec lemma first
  deriving Repr, BEq, Inhabited

def classifyEdge (decl dep : Name) : MetaM EdgeClass := do
  let fp ← footprint decl
  let inStmt := fp.stmt.contains dep
  if !inStmt && !fp.proof.contains dep then return .none
  let unf := (← probe decl dep) == .unfold
  return match inStmt, unf with
    | true, true => .stmtUnfold
    | true, false => .stmt
    | false, true => .unfold
    | false, false => .proofOnly

/-- Summary of an analysis run over a module prefix. -/
structure Report where
  decls      : Nat
  stmtEdges  : Nat
  proofEdges : Nat
  instEdges  : Nat
  simpDecls  : Nat
  nontrivialSCCs : Array (Array Name)
  deriving Repr

/-- Run the v1 analyzer on every declaration in modules starting with `pre`. -/
def analyze (pre : Name) : MetaM Report := do
  let ds ← declsInModules pre
  let mut adj : NameMap (Array Name) := {}
  let mut s := 0; let mut p := 0; let mut i := 0; let mut k := 0
  for d in ds do
    let fp ← footprint d
    s := s + fp.stmt.size; p := p + fp.proof.size; i := i + fp.inst.size
    if fp.simp then k := k + 1
    adj := adj.insert d (fp.stmt ++ fp.proof)
  let comps := (sccs ds adj).filter (·.size > 1)
  return { decls := ds.size, stmtEdges := s, proofEdges := p, instEdges := i,
           simpDecls := k, nontrivialSCCs := comps }

end Decouple
