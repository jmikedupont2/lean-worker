import RequestProject.Analyzer

/-!
# Module-level footprints and minimal imports (v1 "done when" check)

For a loaded module `M`, the *constant footprint* of `M` is the set of modules that
define some constant occurring in the type or value of a declaration of `M`
(compiler-generated auxiliaries of `M` included, since they belong to `M`).

* `neededModules M` – that set, minus `M` itself;
* `minimalImports M` – its antichain under the transitive import order (drop every
  module already reachable from another needed module).  This is the constant-level
  analogue of Mathlib's `#min_imports`;
* `uncoveredImports M` – direct imports of `M` that provide no module of
  `minimalImports M`.  These are what `shake` would flag *on constant evidence alone*;
  they are either removable or needed for an invisible reason (notation, tactics,
  attributes, instances found only during elaboration).
-/

open Lean Meta

namespace Decouple

/-- Index of a module name in the current environment header. -/
def moduleIdx? (env : Environment) (m : Name) : Option Nat :=
  env.header.moduleNames.findIdx? (· == m)

/-- Direct imports of a loaded module. -/
def directImports (env : Environment) (m : Name) : Array Name :=
  match moduleIdx? env m with
  | some i => env.header.moduleData[i]!.imports.map (·.module)
  | none => #[]

/-- Transitive import closure of every loaded module, computed once (modules are
stored in topological order in the header, so one forward pass suffices). -/
def importClosure (env : Environment) : NameMap NameSet := Id.run do
  let mut out : NameMap NameSet := {}
  for m in env.header.moduleNames do
    let mut s : NameSet := {}
    for i in directImports env m do
      s := s.insert i
      for j in (out.find? i).getD {} do s := s.insert j
    out := out.insert m s
  return out

/-- All constants (including compiler-generated ones) defined in module `m`. -/
def constantsOfModule (env : Environment) (m : Name) : Array ConstantInfo :=
  match moduleIdx? env m with
  | some idx => env.header.moduleData[idx]!.constNames.filterMap env.find?
  | none => #[]

/-- Modules defining some constant used (in a type or value) by a declaration of `m`. -/
def neededModules (env : Environment) (m : Name) : NameSet := Id.run do
  let mut out : NameSet := {}
  for ci in constantsOfModule env m do
    for c in ci.type.getUsedConstants ++ valueConsts ci do
      let some j := env.getModuleIdxFor? c | continue
      let mj := env.header.moduleNames[j.toNat]!
      if mj != m then out := out.insert mj
  return out

/-- Antichain of `needed` under the transitive import order. -/
def minimizeModules (clos : NameMap NameSet) (needed : NameSet) : Array Name :=
  needed.toArray.filter fun a =>
    !needed.toArray.any fun b => b != a && ((clos.find? b).getD {}).contains a

/-- Constant-level minimal imports of `m` (`clos` is `importClosure env`, computed once). -/
def minimalImports (env : Environment) (clos : NameMap NameSet) (m : Name) : Array Name :=
  minimizeModules clos (neededModules env m)

/-- Direct imports of `m` that do not provide any module of the constant-level minimal
import set (neither directly nor transitively). -/
def uncoveredImports (env : Environment) (clos : NameMap NameSet) (m : Name) : Array Name :=
  let mins := minimizeModules clos (neededModules env m)
  (directImports env m).filter fun i =>
    !(mins.contains i || mins.any (((clos.find? i).getD {}).contains ·))

/-- Sanity check: every needed module is reachable from the declared imports. -/
def importsSound (env : Environment) (clos : NameMap NameSet) (m : Name) : Bool :=
  (neededModules env m).toArray.all ((clos.find? m).getD {}).contains

end Decouple
