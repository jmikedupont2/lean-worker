import RequestProject.Analyzer

/-!
# Anchoring declarations in a textbook schema

The pure side (placement, refinement, excess) is `RequestProject/Ontology.lean`. This file is the
metaprogram that turns a Lean environment into the *anchors* that the placement starts from.

* The schema is read from a JSON file (`tools/ontology/textbook.json`): a list of concepts
  (textbook sections) with their chapter, their prerequisite sections (`after`, written by hand),
  and the Mathlib classes that stand for them (`anchors`).
* `classAnchors K`: an anchor class stands for its own concept. Any other class stands for the
  concepts of the classes it is built from: its structure parents (`extends`) and the classes in
  its own type (instance parameters such as `[LE α]`), recursively. So Mathlib classes that are
  not in the schema (`CompleteLinearOrder`, `IsOrderedRing`, `IsTopologicalGroup`, …) are placed
  automatically, possibly across several mother structures.
* `constAnchors c`: a class is anchored as above; any other constant by the classes that occur in
  its type (one hop, so `Lattice.toSemilatticeSup` counts as `Lattice` and `SemilatticeSup`).
* `declAnchors d`: the statement anchors are those of the constants of `d`'s type (plus `d` itself
  if it is a class); the proof anchors are those of the proof footprint of `d` (constants of the
  value that are not in the statement, with compiler auxiliaries folded in, see `footprint`).
-/

open Lean Meta

namespace Decouple.Schema

structure Concept where
  name    : String
  chapter : String
  after   : Array String
  anchors : Array Name
  deriving Inhabited

structure Schema where
  level0   : Array String
  level1   : Array (String × String)
  concepts : Array Concept
  deriving Inhabited

/-- Several schema files combined into one ontology (concept names must be distinct;
prerequisites may refer to concepts of another file). -/
def Schema.append (a b : Schema) : Schema :=
  { level0 := a.level0 ++ b.level0, level1 := a.level1 ++ b.level1,
    concepts := a.concepts ++ b.concepts }

def Schema.idx (s : Schema) (n : String) : Option Nat := s.concepts.findIdx? (·.name == n)

private def getStr (j : Json) (k : String) : Except String String := do (← j.getObjVal? k).getStr?

def loadSchema (path : System.FilePath) : IO Schema := do
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let r : Except String Schema := do
    let l0 ← (← j.getObjVal? "level0").getArr?
    let l0 ← l0.mapM (·.getStr?)
    let l1o ← (← j.getObjVal? "level1").getObj?
    let l1 ← l1o.toArray.mapM fun ⟨k, v⟩ => do return (k, ← v.getStr?)
    let cs ← (← j.getObjVal? "concepts").getArr?
    let cs ← cs.mapM fun c => do
      let after ← (← (← c.getObjVal? "after").getArr?).mapM (·.getStr?)
      let anchors ← (← (← c.getObjVal? "anchors").getArr?).mapM (·.getStr?)
      return { name := ← getStr c "name", chapter := ← getStr c "chapter", after,
               anchors := anchors.map String.toName : Concept }
    return { level0 := l0, level1 := l1, concepts := cs }
  IO.ofExcept r

def loadSchemas (paths : List System.FilePath) : IO Schema := do
  let mut s : Schema := { level0 := #[], level1 := #[], concepts := #[] }
  for p in paths do s := s.append (← loadSchema p)
  return s

/-- The anchor classes of the schema. -/
def Schema.anchorSet (s : Schema) : NameSet :=
  s.concepts.foldl (fun acc c => c.anchors.foldl (·.insert ·) acc) {}

/-- The classes a class is built from: structure parents and the classes in its type. -/
def classPrereqs (env : Environment) (k : Name) : Array Name := Id.run do
  let ps := if isStructure env k then (getStructureParentInfo env k).map (·.structName) else #[]
  let tys := match env.find? k with
    | some ci => ci.type.getUsedConstants.filter fun c => c != k && isClass env c
    | none => #[]
  return (ps ++ tys).foldl (fun acc c => if acc.contains c then acc else acc.push c) #[]

/-- Memoized anchoring of classes. -/
abbrev AnchorM := StateT (NameMap (Array Name)) MetaM

def union (a b : Array Name) : Array Name :=
  b.foldl (fun acc i => if acc.contains i then acc else acc.push i) a

/-- The anchor classes a class stands for: itself if it is an anchor, otherwise the anchors of
the classes it is built from. -/
partial def classAnchors (am : NameSet) (k : Name) : AnchorM (Array Name) := do
  if am.contains k then return #[k]
  if let some r := (← get).find? k then return r
  modify (·.insert k #[])  -- cycle guard
  let env ← getEnv
  let mut out : Array Name := #[]
  for p in classPrereqs env k do
    out := union out (← classAnchors am p)
  modify (·.insert k out)
  return out

/-- Anchors of a constant: an anchor (class or not) stands for itself, a class as in
`classAnchors`, any other constant for the classes and anchors in its type (one hop). -/
def constAnchors (am : NameSet) (c : Name) : AnchorM (Array Name) := do
  let env ← getEnv
  if am.contains c then return #[c]
  if isClass env c then return ← classAnchors am c
  let some ci := env.find? c | return #[]
  let mut out := #[]
  for k in ci.type.getUsedConstants do
    if am.contains k then out := union out #[k]
    else if isClass env k then out := union out (← classAnchors am k)
  return out

def sortNames (xs : Array Name) : Array Name := xs.qsort (·.toString < ·.toString)

/-- Statement and proof anchors (anchor classes) of a declaration. -/
def declAnchors (am : NameSet) (d : Name) : AnchorM (Array Name × Array Name) := do
  let env ← getEnv
  let some ci := env.find? d | return (#[], #[])
  let mut s := #[]
  if isClass env d then s := union s (← classAnchors am d)
  for c in ci.type.getUsedConstants do
    s := union s (← constAnchors am c)
  let fp ← footprint d
  let mut p := #[]
  for c in fp.proof do
    p := union p (← constAnchors am c)
  return (sortNames s, sortNames p)

/-- Mathlib's own prerequisite relation between anchor classes: for every anchor class of the
environment, the anchor classes reachable from it through `classPrereqs` (through any classes,
anchors or not). -/
def anchorReach (s : Schema) : MetaM (Array (Name × Array Name)) := do
  let env ← getEnv
  let am := s.anchorSet
  let mut out := #[]
  for a in am.toArray do
    unless env.contains a do continue
    let mut seen : NameSet := {}
    let mut work := classPrereqs env a
    let mut hits := #[]
    while h : work.size > 0 do
      let c := work[work.size - 1]
      work := work.pop
      if seen.contains c then continue
      seen := seen.insert c
      if am.contains c && c != a then hits := hits.push c
      work := work ++ classPrereqs env c
    out := out.push (a, sortNames hits)
  return out

/-- Every class of the environment with its anchor classes (for the census). -/
def classCensus (s : Schema) : MetaM (Array (Name × Array Name × Name)) := do
  let env ← getEnv
  let am := s.anchorSet
  let classes := env.constants.fold (init := #[]) fun acc n _ =>
    if isClass env n && !n.isInternal then acc.push n else acc
  let (rows, _) ← (classes.mapM fun k => do
    let mod : Name := match env.getModuleIdxFor? k with
      | some i => env.header.moduleNames[i.toNat]!
      | none => Name.anonymous
    return (k, sortNames (← classAnchors am k), mod)).run {}
  return rows

def Schema.json (s : Schema) : Json :=
  Json.mkObj [
    ("level0", toJson s.level0),
    ("level1", Json.mkObj (s.level1.toList.map fun (k, v) => (k, toJson v))),
    ("concepts", toJson (s.concepts.map fun c => Json.mkObj [
      ("name", toJson c.name), ("chapter", toJson c.chapter), ("after", toJson c.after),
      ("anchors", toJson (c.anchors.map toString))]))]

end Decouple.Schema
