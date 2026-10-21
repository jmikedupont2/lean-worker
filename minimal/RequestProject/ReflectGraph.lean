import RequestProject.Analyzer
import RequestProject.Reflect

/-!
# Reifying a chunk partition as a `DeclGraph`

`decouple_graph g chunks [[A, A_spec], [B₁, B₂]]` or
`decouple_graph g modules [M₁, M₂]` (or `decouple_graph g imports [M₁, M₂]`) reads the given chunks (lists of declarations, or all
user-facing declarations of modules) in order, numbers the declarations, computes their
statement and proof edges with `footprint`, and adds two definitions:

* `g : Decouple.Reflect.DeclGraph`, a closed literal, in which chunk `k` may use every chunk
  `j < k` (so the graph is `Layered`);
* `g.names : Array Lean.Name`, the declaration behind each number (for error reports).

With `imports`, chunk `k` may use chunk `j` only if module `k` imports module `j` (directly or
through modules of the list), instead of every `j < k`; the graph is then `Layered` exactly when
the modules are listed in an order compatible with the imports.

Edges to declarations outside the chunks are dropped: they point below the partition.
A theorem `g.NoBackEdge` can then be proved by `noBackEdge_of_valid (by decide +kernel)`.

This metaprogram is not verified: the proofs in `RequestProject/Reflect.lean` are about the
data it produces.
-/

open Lean Elab Command Meta

namespace Decouple.Reflect

/-- User-facing declarations of a module (same filter as the fingerprint gate). -/
def userDeclsOfModule (env : Environment) (m : Name) : Array Name :=
  ((env.header.moduleNames.idxOf? m).map fun idx =>
    env.header.moduleData[idx]!.constNames.filter fun n =>
      collapse n == n && !n.isInternal).getD #[]

/-- Reify a sequence of chunks. -/
def reifyChunks (chunks : Array (Array Name)) (allowed? : Option (Array (Nat × Nat)) := none) :
    MetaM (DeclGraph × Array Name) := do
  let mut names : Array Name := #[]
  let mut chunkOf : Array Nat := #[]
  let mut idx : NameMap Nat := {}
  for h : k in [0:chunks.size] do
    for n in chunks[k] do
      if idx.contains n then throwError "{n} occurs in more than one chunk"
      idx := idx.insert n names.size
      names := names.push n
      chunkOf := chunkOf.push k
  let mut edges : Array (Nat × Nat) := #[]
  for h : i in [0:names.size] do
    let fp ← footprint names[i]
    for t in fp.stmt ++ fp.proof do
      if let some j := idx.find? t then edges := edges.push (i, j)
  let mut linear : Array (Nat × Nat) := #[]
  for a in [0:chunks.size] do
    for b in [0:a] do linear := linear.push (a, b)
  let allowed := allowed?.getD linear
  return ({ chunkOf := chunkOf.toList, edges := edges.toList, mayDependOn := allowed.toList },
    names)

def DeclGraph.toExpr (g : DeclGraph) : Expr :=
  mkApp3 (mkConst ``DeclGraph.mk) (Lean.toExpr g.chunkOf) (Lean.toExpr g.edges)
    (Lean.toExpr g.mayDependOn)

syntax (name := decoupleGraph) "decouple_graph " ident &" chunks " "[" ("[" ident,* "]"),* "]" :
  command
syntax (name := decoupleGraphModules) "decouple_graph " ident &" modules " "[" ident,* "]" :
  command
syntax (name := decoupleGraphImports) "decouple_graph " ident &" imports " "[" ident,* "]" :
  command

/-- Pairs `(a, b)` of positions in `ms` such that module `ms[a]` imports module `ms[b]`,
directly or through other modules *of the list*. Import paths through modules outside the list
are not followed, so the relation can only be smaller than the true transitive import relation
(a stricter check). -/
def importClosure (env : Environment) (ms : Array Name) : Array (Nat × Nat) := Id.run do
  let direct : Array (Array Nat) := ms.map fun m =>
    match env.header.moduleNames.idxOf? m with
    | some idx => env.header.moduleData[idx]!.imports.filterMap fun i => ms.idxOf? i.module
    | none => #[]
  let mut out : Array (Nat × Nat) := #[]
  for a in [0:ms.size] do
    let mut seen : Array Bool := Array.replicate ms.size false
    let mut todo := direct[a]!
    while !todo.isEmpty do
      let b := todo.back!
      todo := todo.pop
      unless seen[b]! do
        seen := seen.set! b true
        todo := todo ++ direct[b]!
    for b in [0:ms.size] do
      if seen[b]! && b != a then out := out.push (a, b)
  return out

def addGraph (g : Name) (chunks : Array (Array Name)) (allowed? : Option (Array (Nat × Nat)) := none) :
    CommandElabM Unit := do
  let (graph, names) ← liftTermElabM <| reifyChunks chunks allowed?
  let g ← liftCoreM <| (do
    let ns ← getCurrNamespace
    return ns ++ g)
  liftCoreM <| addAndCompile <| .defnDecl {
    name := g, levelParams := [], type := mkConst ``DeclGraph, value := graph.toExpr,
    hints := .abbrev, safety := .safe }
  liftCoreM <| addAndCompile <| .defnDecl {
    name := g ++ `names, levelParams := [], type := mkApp (mkConst ``Array [0]) (mkConst ``Name),
    value := Lean.toExpr names, hints := .abbrev, safety := .safe }
  logInfo m!"{g}: {names.size} declarations in {chunks.size} chunks, {graph.edges.length} edges"

elab_rules : command
  | `(decouple_graph $g:ident chunks [$[[$cs,*]],*]) => do
    let chunks ← cs.mapM fun c => c.getElems.mapM fun n =>
      liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
    addGraph g.getId chunks

elab_rules : command
  | `(decouple_graph $g:ident modules [$ms,*]) => do
    let env ← getEnv
    let chunks := ms.getElems.map fun m => userDeclsOfModule env m.getId
    for m in ms.getElems, c in chunks do
      if c.isEmpty then throwError "module {m.getId} has no declarations (is it imported?)"
    addGraph g.getId chunks

elab_rules : command
  | `(decouple_graph $g:ident imports [$ms,*]) => do
    let env ← getEnv
    let mods := ms.getElems.map (·.getId)
    let chunks := mods.map fun m => userDeclsOfModule env m
    for m in mods, c in chunks do
      if c.isEmpty then throwError "module {m} has no declarations (is it imported?)"
    addGraph g.getId chunks (some (importClosure env mods))

end Decouple.Reflect
