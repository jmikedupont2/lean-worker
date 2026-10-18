import RequestProject.ModuleDeps
import RequestProject.Classify

/-!
# Verification gate: declaration fingerprints

A *fingerprint* of a user-facing declaration records what a refactor must not change:

* its name,
* its statement (a hash of the elaborated type, syntactic up to binder names),
* the axioms it depends on (`#print axioms`),
* whether it is `@[simp]` and whether it is an instance (attribute edges: a refactor that
  drops or adds one of these silently changes other proofs).

`fingerprints mods` computes them for every user-facing declaration of the given modules;
`compareFingerprints` reports every difference. A refactor is accepted only if the
fingerprints of the original module(s) and of the refactored module(s) coincide.
-/

open Lean Meta

namespace Decouple

/-- One line per declaration: `name|statement-hash|axioms|simp|instance`. -/
def fingerprint (n : Name) : MetaM String := do
  let env ← getEnv
  let some ci := env.find? n | throwError "unknown constant {n}"
  let axs := (← collectAxioms n).qsort Name.lt
  let simp ← isSimpLemma n
  let inst := isInstanceCore env n
  return s!"{n}|{hash ci.type}|{axs.toList}|simp={simp}|inst={inst}"

/-- Fingerprints of every user-facing declaration of the given modules, sorted by name. -/
def fingerprints (mods : Array Name) : MetaM (Array String) := do
  let env ← getEnv
  let mut out := #[]
  for m in mods do
    for ci in constantsOfModule env m do
      let n := ci.name
      if collapse n != n || n.isInternal then continue
      out := out.push (← fingerprint n)
  return out.qsort (· < ·)

/-- Lines present in one fingerprint set but not the other. -/
def compareFingerprints (before after : Array String) : Array String × Array String :=
  (before.filter (!after.contains ·), after.filter (!before.contains ·))

end Decouple
