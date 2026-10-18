import Lean

/-!
# Trust capsules: what checking one declaration needs, layer by layer

A capsule for a declaration `D` lists what a re-check of `D` depends on, from the term down:

1. **expr + proof**: the transitive closure of constants that `D`'s statement and value mention
   (through the statements and values of those constants), by kind, and its axioms;
2. **kernel features**: which parts of the kernel the closure can exercise: inductive types and
   ι-reduction (recursors), structure projections (`Expr.proj`), quotients (`Quot.*`), `Nat` and
   `String` literals and the kernel's `Nat` acceleration (GMP), and `Lean.ofReduceBool` /
   `Lean.trustCompiler` (which put the compiler, the interpreter and native code in the trusted
   base).

`tools/trust_capsule.py` maps the features to the kernel's C++ functions, sizes their machine
code in the shipped `libleanshared.so`, and records the remaining layers (runtime, shared
libraries, operating system, bootstrap chain) that are not measured here.

This is a *dependency* report, not a proof: the closure over-approximates what the kernel
actually unfolds when it checks `D` (it follows every value, not only the ones reduced).
-/

open Lean

namespace Decouple.Capsule

/-- Constants the kernel accelerates on `Nat` literals (GMP-backed in the C++ kernel). -/
def natAccel : List Name :=
  [``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.div, ``Nat.mod, ``Nat.gcd, ``Nat.beq, ``Nat.ble,
   ``Nat.land, ``Nat.lor, ``Nat.xor, ``Nat.shiftLeft, ``Nat.shiftRight, ``Nat.pow, ``Nat.log2]

structure Capsule where
  decl : Name
  closure : Nat := 0
  kinds : Std.HashMap String Nat := {}
  axioms : Array Name := #[]
  recursors : Nat := 0
  inductives : Nat := 0
  projections : Bool := false
  quot : Bool := false
  natLit : Bool := false
  strLit : Bool := false
  natAccel : Array Name := #[]
  compilerTrusted : Bool := false
  /-- The closure itself (sorted), so that downstream tools can carry the constant list. -/
  constants : Array Name := #[]

def kindOf : ConstantInfo → String
  | .thmInfo _ => "theorem" | .axiomInfo _ => "axiom" | .defnInfo _ => "definition"
  | .opaqueInfo _ => "opaque" | .inductInfo _ => "inductive" | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor" | .quotInfo _ => "quot"

/-- Compute the capsule of `d` in the current environment. -/
def capsule (d : Name) : CoreM Capsule := do
  let env ← getEnv
  let mut seen : NameHashSet := {}
  let mut todo : Array Name := #[d]
  let mut c : Capsule := { decl := d }
  while h : todo.size > 0 do
    let n := todo.back
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    let k := kindOf ci
    c := { c with kinds := c.kinds.insert k (c.kinds.getD k 0 + 1) }
    match ci with
    | .axiomInfo _ => c := { c with axioms := c.axioms.push n }
    | .recInfo _ => c := { c with recursors := c.recursors + 1 }
    | .inductInfo _ => c := { c with inductives := c.inductives + 1 }
    | .quotInfo _ => c := { c with quot := true }
    | _ => pure ()
    if natAccel.contains n then c := { c with natAccel := c.natAccel.push n }
    if n == ``Lean.ofReduceBool || n == ``Lean.trustCompiler then
      c := { c with compilerTrusted := true }
    let exprs := [ci.type] ++ (ci.value? (allowOpaque := true)).toList
    for e in exprs do
      if e.find? (·.isProj) |>.isSome then c := { c with projections := true }
      if e.find? (fun x => x matches .lit (.natVal _)) |>.isSome then c := { c with natLit := true }
      if e.find? (fun x => x matches .lit (.strVal _)) |>.isSome then c := { c with strLit := true }
      for u in e.getUsedConstants do
        unless seen.contains u do todo := todo.push u
  return { c with closure := seen.size, axioms := c.axioms.qsort Name.lt,
                  constants := seen.toArray.qsort Name.lt }

def Capsule.toJson (c : Capsule) : Json :=
  Json.mkObj [
    ("decl", Lean.toJson c.decl), ("closure", Lean.toJson c.closure),
    ("kinds", Json.mkObj (c.kinds.toList.map fun (k, v) => (k, Lean.toJson v))),
    ("axioms", Lean.toJson c.axioms), ("constants", Lean.toJson c.constants),
    ("features", Json.mkObj [
      ("inductive", Lean.toJson (decide (c.inductives > 0))), ("recursors", Lean.toJson c.recursors),
      ("projections", Lean.toJson c.projections), ("quot", Lean.toJson c.quot),
      ("natLit", Lean.toJson c.natLit), ("strLit", Lean.toJson c.strLit),
      ("natAccel", Lean.toJson c.natAccel), ("compilerTrusted", Lean.toJson c.compilerTrusted)])]

end Decouple.Capsule
