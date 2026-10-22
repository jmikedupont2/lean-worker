#!/usr/bin/env bash
# job-verifier.sh — TEST_ONLY driver for the PR #25 job-verifier checker.
#
# Usage: job-verifier.sh <submission.lean> <module> <decl> <refModule> <expectedName>
#
# Stage → build (pinned toolchain via lean-toolchain) → CHECK (environment-based).
# Exit: 0 accepted / 1 rejected / 2 driver or checker error.
#
# TEST_ONLY limitations (see JobVerifier/README.md):
#   * no BUILD/CHECK sandbox separation, no uid isolation
#   * no signed offers/attestations, no kernel replay
#   * the driver itself decides the .lean-extension gate (v6) — in production
#     this belongs in the job spec validation, not here.
set -euo pipefail

SRC="$1"; MODULE="$2"; DECL="$3"; REF="$4"; EXPECTED="$5"

if [[ "$SRC" != *.lean ]]; then
  echo "{\"schema\":\"zos.verify.v1-testonly\",\"reasonCode\":\"NOT_LEAN_SOURCE\",\"detail\":\"$SRC\"}"
  exit 1
fi
if [[ ! -s "$SRC" ]]; then
  echo "{\"schema\":\"zos.verify.v1-testonly\",\"reasonCode\":\"EMPTY_SOURCE\"}"
  exit 1
fi

HERE="$(cd "$(dirname "$0")/.." && pwd)"       # minimal/
JV="$HERE/JobVerifier"
STAGE="$(mktemp -d /tmp/jobverifier.XXXXXX)"
trap 'rm -rf "$STAGE"' EXIT

# Pin the toolchain inside the stage: elan resolves per-CWD, and /tmp would
# fall back to the user default (4.35.0), producing oleans the 4.28.0-built
# checker rejects as "incompatible header".
cp "$HERE/lean-toolchain" "$STAGE/lean-toolchain"

cp "$SRC" "$STAGE/$MODULE.lean"

# Build with the toolchain pinned by minimal/lean-toolchain (elan resolves it
# because we run from inside the tree).  The submission builds ALONE: it gets
# no access to the reference module, so it cannot import __expected and
# specialize against it.
(cd "$STAGE" && lean "$MODULE.lean" -o "$MODULE.olean") >&2

# Build the reference module beside it (checker-only input).
REF_SRC="$(dirname "$SRC")/Ref.lean"
[[ -f "$REF_SRC" ]] || REF_SRC="$HERE/JobVerifier/test/cases/$(basename "$(dirname "$SRC")")/Ref.lean"
cp "$REF_SRC" "$STAGE/$REF.lean"
(cd "$STAGE" && lean "$REF.lean" -o "$REF.olean") >&2

export LEAN_PATH="$STAGE"
# Pin the checker's sysroot to the toolchain resolved from minimal/
# (lean-toolchain pins 4.28.0).  Without this, the checker's findSysroot
# follows elan's *invoking-cwd* default (e.g. 4.35.0 from /tmp) and the
# Init oleans come back "incompatible header".
export LEAN_SYSROOT="$(cd "$HERE" && lean --print-prefix)"
exec "$JV/jobverifier" --module "$MODULE" --decl "$DECL" --ref "$REF" --expected "$EXPECTED"
