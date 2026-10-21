/-
# JobVerifier.Check — TEST_ONLY PR #25 remediation checker

Implements the CHECK-sandbox decision from the independent audit's
remediation design (`STEP25_PR25_REMEDIATION_DESIGN.md` §4.3):

  * decide from the elaborated ENVIRONMENT, never from lexer output
  * `env.find? decl` must be a `thmInfo` defined in the submission module
  * `c.type` must be structurally equal to the reference `__expected : Prop`
  * `Lean.collectAxioms` over the environment (closes sorry/private/raw-string
    lexer bypasses as a class)
  * any axiom DECLARED in the submission module fails (AXIOM_DECLARED)

Exit codes: 0 = accepted, 1 = rejected (reason on stdout), 2 = checker error.
This is TEST_ONLY: no sandbox, no signatures, no kernel replay yet.
See README.md for what is and is not covered.
-/
import Lean

open Lean

inductive Reason where
  | ok | targetMissing | targetNotTheorem | statementMismatch
  | sorryAxiom | axiomNotAllowed | axiomDeclared
  | importFailed | checkerError
  deriving Inhabited, Repr

def Reason.code : Reason → String
  | .ok => "OK"
  | .targetMissing => "TARGET_MISSING"
  | .targetNotTheorem => "TARGET_NOT_THEOREM"
  | .statementMismatch => "STATEMENT_MISMATCH"
  | .sorryAxiom => "SORRY"
  | .axiomNotAllowed => "AXIOM_NOT_ALLOWED"
  | .axiomDeclared => "AXIOM_DECLARED"
  | .importFailed => "IMPORT_FAILED"
  | .checkerError => "CHECKER_ERROR"

structure Cfg where
  module : Name
  decl : Name
  refModule : Name
  expectedName : Name
  allowedAxioms : List Name

def verdict (r : Reason) (cfg : Cfg) (axioms : List Name := [])
    (declared : List Name := []) (extra : String := "") : IO Unit := do
  let q (n : Name) := s!"\"{n}\""
  let axStr := String.intercalate ", " (axioms.map q)
  let dclStr := String.intercalate ", " (declared.map q)
  IO.println s!"{\"schema\":\"zos.verify.v1-testonly\",\"jobModule\":\"{cfg.module}\",\"decl\":\"{cfg.decl}\",\"reasonCode\":\"{r.code}\",\"axioms\":[{axStr}],\"declaredAxiomsInSubmission\":[{dclStr}]{extra}}"

/-- All constants defined in `mod` whose ConstantInfo is an axiomInfo. -/
def declaredAxioms (env : Environment) (mod : Name) : List Name := Id.run do
  let some idx := env.getModuleIdxFor? mod | []
  let some md := env.header.moduleData[idx]? | []
  md.constNames.foldl (init := []) fun acc n =>
    match env.find? n with
    | some (.axiomInfo _) => n :: acc
    | _ => acc

/-- The full decision procedure. Exit 0 accepted / 1 rejected / 2 checker error. -/
def run (cfg : Cfg) : IO UInt32 := do
  initSearchPath
  let env ←
    try
      importModules
        #[{ module := cfg.refModule, runtimeOnly := false },
          { module := cfg.module, runtimeOnly := false }]
        (opts := {}) (trustLevel := 0)
    catch e =>
      verdict .importFailed cfg (extra := s!",\"detail\":\"{e}\"")
      return 1
  let some expectedInfo := env.find? cfg.expectedName
    | do
        verdict .checkerError cfg (extra := ",\"detail\":\"reference __expected missing\"")
        return 2
  let some c := env.find? cfg.decl
    | do verdict .targetMissing cfg; return 1
  let .thmInfo thm := c
    | do verdict .targetNotTheorem cfg; return 1
  -- The declaration must be defined in the submission module, not imported.
  if env.getModuleFor? cfg.decl != some cfg.module then
    verdict .targetMissing cfg (extra := ",\"detail\":\"decl not defined in submission module\"")
    return 1
  -- Level parameters and type must match the reference structurally.
  if c.levelParams != expectedInfo.levelParams || thm.type != expectedInfo.type then
    verdict .statementMismatch cfg; return 1
  -- Axioms from the environment (no lexer involved).
  let (axioms, _) ← (Lean.collectAxioms cfg.decl).toIO
    { fileName := "<jobverifier>", fileMap := default } { env := env }
  if axioms.contains `sorryAx then
    verdict .sorryAxiom cfg (axioms := axioms); return 1
  let bad := axioms.filter (· ∉ cfg.allowedAxioms)
  if !bad.isEmpty then
    verdict .axiomNotAllowed cfg (axioms := axioms); return 1
  -- The submission must not declare axioms of its own (defence in depth).
  let declared := declaredAxioms env cfg.module
  if !declared.isEmpty then
    verdict .axiomDeclared cfg (declared := declared); return 1
  verdict .ok cfg (axioms := axioms)
  return 0

def parseArgs : List String → Option Cfg
  | ["--module", m, "--decl", d, "--ref", r, "--expected", e] =>
    some { module := m.toName, decl := d.toName, refModule := r.toName,
           expectedName := e.toName,
           allowedAxioms := [`propext, `Classical.choice, `Quot.sound] }
  | _ => none

def main (args : List String) : IO UInt32 := do
  match parseArgs args with
  | some cfg => run cfg
  | none =>
    IO.eprintln "usage: jobverifier --module M --decl D --ref R --expected E"
    IO.eprintln "  LEAN_PATH must contain the pinned deps and the staged submission olean."
    return 2
