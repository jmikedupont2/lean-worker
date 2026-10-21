import RequestProject.Chunks
import RequestProject.ReflectGraph

/-!
# Demo: the two-declaration case, A and B

Each coupling type from the plan, on a tiny example, with the analyzer's verdict
pinned by `#guard_msgs` so that a change in the coupling fails the build.
-/

open Lean Meta Decouple

namespace DemoAB

/-- `A`: a concrete definition. -/
def A (n : Nat) : Nat := n + n

/-- An API lemma for `A`: its spec. -/
theorem A_spec (n : Nat) : A n = 2 * n := by unfold A; omega

/-- `B₁` uses `A` only through its statement, proved via the API lemma:
a statement edge, no unfold edge. -/
theorem B₁ (n : Nat) : A n = n * 2 := by rw [A_spec, Nat.mul_comm]

/-- `B₂` is proved by `rfl`: it relies on `A` unfolding (definitional coupling). -/
theorem B₂ : A 3 = 6 := rfl

/-- `B₃` mentions only `2 * n` in its statement; `A` occurs only in the proof
(proof-only coupling: can be reproved without `A`). -/
theorem B₃ (n : Nat) : 2 * n = n + n := (A_spec n).symm.trans rfl

end DemoAB

/-- info: #[`DemoAB.A] -/
#guard_msgs in
#eval show MetaM _ from return (← footprint ``DemoAB.B₁).stmt.filter (· == ``DemoAB.A)

/-- info: #[] -/
#guard_msgs in
#eval show MetaM _ from unfoldEdges ``DemoAB.B₁

/-- info: #[`DemoAB.A] -/
#guard_msgs in
#eval show MetaM _ from unfoldEdges ``DemoAB.B₂

/-- info: Decouple.EdgeClass.stmt -/
#guard_msgs in
#eval show MetaM _ from classifyEdge ``DemoAB.B₁ ``DemoAB.A

/-- info: Decouple.EdgeClass.stmtUnfold -/
#guard_msgs in
#eval show MetaM _ from classifyEdge ``DemoAB.B₂ ``DemoAB.A

/-- info: Decouple.EdgeClass.unfold -/
#guard_msgs in
#eval show MetaM _ from classifyEdge ``DemoAB.B₃ ``DemoAB.A

/-- Regression guard: `A` must not depend back on `B₁` (edge direction assertion). -/
example : True := by
  run_tac do
    let fp ← footprint ``DemoAB.A
    if (fp.stmt ++ fp.proof).contains ``DemoAB.B₁ then
      throwError "back-edge A → B₁ introduced"
  trivial

/-! ## Cycles: a mutual block is one SCC (atomic unless the cycle is broken) -/

namespace DemoCycle
mutual
  def isEven : Nat → Bool
    | 0 => true
    | n + 1 => isOdd n
  def isOdd : Nat → Bool
    | 0 => false
    | n + 1 => isEven n
end
end DemoCycle

/-- info: #[#[`DemoCycle.isOdd, `DemoCycle.isEven]] -/
#guard_msgs in
#eval show MetaM _ from do
  let ds := #[``DemoCycle.isEven, ``DemoCycle.isOdd]
  let mut adj : NameMap (Array Name) := {}
  for d in ds do
    let fp ← footprint d
    adj := adj.insert d (fp.stmt ++ fp.proof)
  return (sccs ds adj).filter (·.size > 1)

/-! ## v2 labels and v3 proposals on the A/B example -/

/-- The analysed subtree: here, the definitions of the `DemoAB` namespace. -/
def demoTargets : NameSet := NameSet.empty.insert ``DemoAB.A

/-! `A_spec` is a fixed point: it is proved from `A`'s definition and no earlier lemma about `A`
can replace that. `B₂` is abstractable even though it sits next to `A`: `A_spec` / `B₁`
already prove it without unfolding `A`. -/

/-- info: [(`DemoAB.B₁, "clean"), (`DemoAB.B₂, "abstractable"), (`DemoAB.B₃, "abstractable"), (`DemoAB.A_spec, "fixed")] -/
#guard_msgs in
#eval show MetaM _ from do
  let ds := [``DemoAB.B₁, ``DemoAB.B₂, ``DemoAB.B₃, ``DemoAB.A_spec]
  ds.mapM fun d => return (d, toString (← labelDecl d demoTargets).label)

/-! v3: proposals for the two edges that rely on `A`'s definition. `B₂` is reproved by
rewriting with `A`'s existing API; `B₃` keeps its proof, with one rewrite along an extracted
spec lemma (`A`'s defining equation) inserted where it used to unfold `A`. Both new proofs
are checked with `A` irreducible and kernel-checked against the unchanged statement. -/

#eval show MetaM Unit from do
  for d in [``DemoAB.B₂, ``DemoAB.B₃] do
    match ← propose d ``DemoAB.A with
    | some p => logInfo m!"{p.decl}: {p.strategy} using {p.lemmas}\n  new proof: {p.proof}"
    | none => logInfo m!"{d}: no proposal"

/-- info: [some "api", some "patch-extract, 1 rewrite point(s)"] -/
#guard_msgs in
#eval show MetaM _ from
  [``DemoAB.B₂, ``DemoAB.B₃].mapM fun d => return (← propose d ``DemoAB.A).map (·.strategy)

/-- The scratch environment is discarded: no proposal or extracted lemma leaks out. -/
example : True := by
  run_tac do
    let env ← getEnv
    if env.contains `DemoAB.A.decouple_spec || env.contains `DemoAB.B₃.decouple_proposal then
      throwError "scratch declarations leaked"
  trivial

/-! ## v5/v6: chunks, cut cost and the back-edge guard on the A/B example

Two chunks: `spec` = {`A`, `A_spec`} below `client` = {`B₁`, `B₂`, `B₃`}. -/

def demoChunk (n : Name) : Option Name :=
  if n == ``DemoAB.A || n == ``DemoAB.A_spec then some `spec
  else if [``DemoAB.B₁, ``DemoAB.B₂, ``DemoAB.B₃].contains n then some `client
  else none

def demoDecls : Array Name :=
  #[``DemoAB.A, ``DemoAB.A_spec, ``DemoAB.B₁, ``DemoAB.B₂, ``DemoAB.B₃]

-- Cut cost of the boundary: one interface edge (`B₁`) and two coupling edges (`B₂`, `B₃`).
/-- info: #[((`client, `spec), 1, 2)] -/
#guard_msgs in
#eval show MetaM _ from do
  return boundaryCosts (← typedEdges demoDecls demoTargets) demoChunk

/-- The intended direction holds: `client` may depend on `spec`, not conversely. -/
example : True := by
  run_tac assertNoBackEdges demoDecls demoChunk fun a b => a == `client && b == `spec
  trivial

-- With the direction reversed, every client → spec edge is reported as a back-edge.
/--
info: #[(`DemoAB.B₁, `DemoAB.A), (`DemoAB.B₁, `DemoAB.A_spec), (`DemoAB.B₂, `DemoAB.A), (`DemoAB.B₃, `DemoAB.A),
  (`DemoAB.B₃, `DemoAB.A_spec)]
-/
#guard_msgs in
#eval show MetaM _ from
  backEdges demoDecls demoChunk fun a b => a == `spec && b == `client

/-! ## Reflective guard: a proved "no back-edge" theorem instead of a shell check

The same partition, reified as data. The checker runs in the kernel, and
`DeclGraph.noBackEdge_of_valid` turns its `true` into the theorem `NoBackEdge`. -/

open Decouple.Reflect in
/-- info: demoGraph: 5 declarations in 2 chunks, 6 edges -/
#guard_msgs in
decouple_graph demoGraph chunks [[DemoAB.A, DemoAB.A_spec], [DemoAB.B₁, DemoAB.B₂, DemoAB.B₃]]

open Decouple.Reflect in
/-- `client` uses `spec` only downward: every edge of the reified graph goes from a chunk to
itself or to the chunk below. -/
theorem demoGraph_noBackEdge : demoGraph.NoBackEdge :=
  DeclGraph.noBackEdge_of_valid (by decide +kernel)

open Decouple.Reflect in
/-- Consequence: along any dependency path, of any length, the chunk number never increases. -/
theorem demoGraph_paths_downward {i j a b : Nat} (hr : demoGraph.Reach i j)
    (ha : demoGraph.chunk? i = some a) (hb : demoGraph.chunk? j = some b) : b ≤ a :=
  DeclGraph.chunk_le_of_reach demoGraph_noBackEdge
    (DeclGraph.layered_of_layeredB (by decide +kernel)) hr ha hb

-- With the chunks in the opposite order the checker returns `false`, and by completeness
-- that means a real back-edge exists.
/-- info: demoGraphReversed: 5 declarations in 2 chunks, 6 edges -/
#guard_msgs in
decouple_graph demoGraphReversed chunks [[DemoAB.B₁, DemoAB.B₂, DemoAB.B₃], [DemoAB.A, DemoAB.A_spec]]

open Decouple.Reflect in
example : ∃ e ∈ demoGraphReversed.edges, demoGraphReversed.edgeOk e = false :=
  DeclGraph.exists_backEdge_of_valid_false (by decide +kernel)
