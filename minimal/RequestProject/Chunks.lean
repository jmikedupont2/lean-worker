import RequestProject.Classify

/-!
# v5/v6: chunk boundaries, cut cost, and edge-direction guards

## Cut cost of a boundary

Given a partition of declarations into chunks, every edge `D → A` from one chunk to another
is classified as in v2 (`stmt`, `proofOnly`, `unfold`, `stmtUnfold`). Interface (`stmt`)
edges are free; every other edge to a definition is *coupling* that has to be abstracted
for the boundary to be a clean seam. The **cut cost** of a boundary is the number of such
edges. Low cost means a natural seam.

## Splitting one module

Source order is a topological order of a module's declarations (Lean is declare-before-use),
so cutting a module at a declaration `D_k` into a prefix chunk and a suffix chunk (the suffix
importing the prefix) never creates a back-edge. `seams` scores every such cut by its cut
cost and balance; `bestSeams` ranks them.

## Regression guard (v6)

`backEdges` lists every edge that goes from a chunk to a chunk it is not allowed to depend on;
`assertNoBackEdges` turns a non-empty list into an error, so that a guard placed in a file
fails the build when a new back-edge appears.
-/

open Lean Meta

namespace Decouple

/-- A typed cross-chunk edge. -/
structure CrossEdge where
  src : Name
  dst : Name
  cls : EdgeClass
  deriving Inhabited

/-- Is this edge coupling (i.e. not a free interface edge)? -/
def EdgeClass.isCoupling : EdgeClass → Bool
  | .proofOnly | .unfold | .stmtUnfold => true
  | _ => false

/-- Typed edges from `decls` to definitions in `targets` (probe included). -/
def typedEdges (decls : Array Name) (targets : NameSet) : MetaM (Array CrossEdge) := do
  let env ← getEnv
  let mut out := #[]
  for d in decls do
    let fp ← footprint d
    for t in fp.stmt ++ fp.proof do
      unless targets.contains t && isProbeTarget env t do continue
      out := out.push { src := d, dst := t, cls := ← classifyEdge d t }
  return out

/-- Cut cost per ordered pair of chunks `(from, to)`: (interface edges, coupling edges). -/
def boundaryCosts (edges : Array CrossEdge) (chunkOf : Name → Option Name) :
    Array ((Name × Name) × (Nat × Nat)) := Id.run do
  let mut m : Std.HashMap (Name × Name) (Nat × Nat) := {}
  for e in edges do
    let some a := chunkOf e.src | continue
    let some b := chunkOf e.dst | continue
    if a == b then continue
    let (i, c) := m.getD (a, b) (0, 0)
    m := m.insert (a, b) (if e.cls.isCoupling then (i, c + 1) else (i + 1, c))
  return m.toArray

/-- Source position (line) of a declaration, if known. -/
def declLine (n : Name) : MetaM Nat := do
  return ((← findDeclarationRanges? n).map (·.range.pos.line)).getD 0

/-- A candidate cut of one module just before declaration `before`. -/
structure Seam where
  before   : Name
  line     : Nat
  prefixSz : Nat
  suffixSz : Nat
  cost     : Nat           -- coupling edges from the suffix into the prefix
  crossing : Array CrossEdge
  deriving Inhabited

/-- Score every cut of the module `m` (between consecutive declarations in source order). -/
def seams (m : Name) : MetaM (Array Seam) := do
  let env ← getEnv
  let ds := (← declsInModules m).filter fun d => (env.getModuleIdxFor? d).isSome
  let mut withLine := #[]
  for d in ds do withLine := withLine.push (d, ← declLine d)
  let sorted := withLine.qsort (fun a b => a.2 < b.2)
  let pos : NameMap Nat := (sorted.mapIdx fun i (d, _) => (d, i)).foldl
    (fun acc (d, i) => acc.insert d i) {}
  let targets : NameSet := ds.foldl (·.insert ·) {}
  let edges ← typedEdges ds targets
  let mut out := #[]
  for k in [1:sorted.size] do
    let crossing := edges.filter fun e =>
      e.cls.isCoupling && (pos.find? e.src).getD 0 ≥ k && (pos.find? e.dst).getD 0 < k
    out := out.push { before := sorted[k]!.1, line := sorted[k]!.2, prefixSz := k,
                      suffixSz := sorted.size - k, cost := crossing.size, crossing }
  return out

/-- Cheapest seams whose smaller side holds at least `minFrac` of the declarations. -/
def bestSeams (ss : Array Seam) (minFrac : Float := 0.25) (n := 5) : Array Seam :=
  let total := ss.foldl (fun _ s => s.prefixSz + s.suffixSz) 0
  let ok := ss.filter fun s =>
    (min s.prefixSz s.suffixSz).toFloat ≥ minFrac * total.toFloat
  (ok.qsort fun a b => a.cost < b.cost || (a.cost == b.cost &&
    (max a.prefixSz a.suffixSz) < (max b.prefixSz b.suffixSz))).extract 0 n

/-- Edges from a chunk to a chunk it may not depend on. -/
def backEdges (decls : Array Name) (chunkOf : Name → Option Name)
    (mayDependOn : Name → Name → Bool) : MetaM (Array (Name × Name)) := do
  let mut out := #[]
  for d in decls do
    let some a := chunkOf d | continue
    let fp ← footprint d
    for t in fp.stmt ++ fp.proof do
      let some b := chunkOf t | continue
      if a != b && !mayDependOn a b then out := out.push (d, t)
  return out

/-- v6 guard: fail if there is any back-edge. -/
def assertNoBackEdges (decls : Array Name) (chunkOf : Name → Option Name)
    (mayDependOn : Name → Name → Bool) : MetaM Unit := do
  let bad ← backEdges decls chunkOf mayDependOn
  unless bad.isEmpty do throwError "back-edges across chunk boundaries: {bad}"

end Decouple
