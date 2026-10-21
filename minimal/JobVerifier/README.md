# JobVerifier — TEST_ONLY PR #25 remediation checker

Implements the CHECK-sandbox decision from the Yku1712 independent audit
(`STEP25_PR25_REMEDIATION_DESIGN.md` §4.3), closing the RT-9 proof-job
substitution class **as a class** instead of patching lexer instances.

## What it does

`Check.lean` builds a standalone `jobverifier` binary that decides acceptance
from the **elaborated environment** — never from scanner/lexer output:

| Check | Reason code on failure |
|---|---|
| `env.find? decl` exists and is a `thmInfo` | `TARGET_MISSING` / `TARGET_NOT_THEOREM` |
| decl is *defined in the submission module* (module-idx match) | `TARGET_MISSING` |
| `thm.type` structurally equal to reference `__expected : Prop` value | `STATEMENT_MISMATCH` |
| `Lean.collectAxioms` (environment-based): no `sorryAx` | `SORRY` |
| axiom policy: `propext`, `Classical.choice`, `Quot.sound` only | `AXIOM_NOT_ALLOWED` |
| no axiom *declared* in the submission module | `AXIOM_DECLARED` |

Exit codes: `0` accepted, `1` rejected (JSON verdict on stdout), `2` checker error.

## Usage

```bash
minimal/scripts/job-verifier.sh <submission.lean> <module> <decl> <refModule> <expectedName>
```

The driver stages the submission in a temp dir, builds it with the toolchain
pinned by `minimal/lean-toolchain` (the submission builds ALONE — it cannot
import the reference), builds the reference beside it, then runs the checker.

## Regression suite

```bash
minimal/JobVerifier/test/run.sh    # 8/8 PASS
```

Reproduces the audit's RT-9 cases: v1 sorry, v2 private-axiom, v3 lexing
confusion (nested comments), v4 statement mismatch, v5 target missing,
v6 non-.lean source, plus honest c0 and submission-axiom c3.

## TEST_ONLY limitations (do NOT ship as-is)

- No BUILD/CHECK sandbox separation or uid isolation (remediation §4.1)
- No signed offers/attestations (§4.2) — verdicts are unauthenticated
- No kernel replay of the proof term (§4.3 last gate)
- Driver (not a validated job spec) decides the `.lean`-extension gate
- `parseName` does not handle escaped dots or numeric name components

## Build

```bash
cd minimal/JobVerifier
lean Check.lean -c Check.c -o Check.olean && leanc -o jobverifier Check.c
```

Toolchain: pinned by `minimal/lean-toolchain` (v4.28.0). The binary and
intermediates (`Check.c`, `Check.olean`, `jobverifier`) are build artifacts —
do not commit them.
