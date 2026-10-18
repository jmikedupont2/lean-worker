import RequestProject.Classify

/-!
# Allowlist of type synonyms that are meant to be unfolded

Some definitions exist only to be unfolded: a *type synonym* such as `OrderDual α := α` or
`Lex α := α` gives a type a second name so it can carry other instances, and its *casts*
(`OrderDual.toDual : α ≃ αᵒᵈ := Equiv.refl α`) are identities. A proof that sees through
them is using them as designed, so an `unfold` edge to one of them is accepted as *fixed by
design* instead of going to the review queue.

Detection is syntactic, so the allowlist is computed rather than written by hand:
* a type synonym is a definition whose type ends in a universe (`… → Sort u`) and whose body,
  under its lambdas, is one of its own arguments;
* a cast is a definition whose body, under its lambdas, is `Equiv.refl _`, `id _` or one of its
  own arguments, and whose type mentions a type synonym.
-/

open Lean Meta

namespace Decouple

/-- Body of a definition under its leading lambdas, with the number of binders. -/
def lambdaBody (e : Expr) : Nat × Expr :=
  go 0 e
where
  go (k : Nat) : Expr → Nat × Expr
    | .lam _ _ b _ => go (k + 1) b
    | .mdata _ b => go k b
    | e => (k, e)

/-- `OrderDual`-style: `def S (α : Sort u) … : Sort u := α`. -/
def isTypeSynonym (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some (.defnInfo v) =>
    let rec resultIsSort : Expr → Bool
      | .forallE _ _ b _ => resultIsSort b
      | .sort _ => true
      | _ => false
    resultIsSort v.type && (lambdaBody v.value).2.isBVar
  | _ => false

/-- `toDual`-style casts: identity body, and a type that mentions a type synonym. -/
def isSynonymCast (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some (.defnInfo v) =>
    let b := (lambdaBody v.value).2
    let identity := b.isBVar || b.isAppOf `Equiv.refl || b.isAppOf ``id
    identity && v.type.getUsedConstants.any (isTypeSynonym env)
  | _ => false

/-- The allowlist: type synonyms and their casts. -/
def isSynonymByDesign (env : Environment) (n : Name) : Bool :=
  isTypeSynonym env n || isSynonymCast env n

end Decouple
