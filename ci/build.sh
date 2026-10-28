#!/usr/bin/env bash
# ci/build.sh — the one gate CI and devs run.  Must execute inside
# `nix develop ./ci` (lean4-nix pins the toolchain from minimal/lean-toolchain).
# Stages: 1) no-mathlib lake build via fast-lakefile.toml
#         2) gokujo knife built from source, then `gokujo check` over the
#            canonical minimal/ module set (exit 0 = clean proofs).
set -uo pipefail
cd "$(dirname "$0")/.."

echo "== toolchain =="
lean --version; lake --version

echo "== stage 1: no-mathlib build =="
cd minimal
cp lakefile.toml lakefile.ci-bak
cp fast-lakefile.toml lakefile.toml
status=0
lake build || status=$?
mv lakefile.ci-bak lakefile.toml
[[ $status -ne 0 ]] && { echo "STAGE 1 FAILED"; exit "$status"; }

echo "== stage 2: gokujo check gate =="
if [[ ! -x ./gokujo-temp ]]; then
  { cat Gokujo.lean; echo 'def main (argv : List String) : IO UInt32 := gokujoMain argv'; } > gokujo-main.lean
  lean -c gokujo-main.c gokujo-main.lean && leanc gokujo-main.c -o gokujo-temp
fi
status=0
./gokujo-temp check \
  Agent.lean APICapabilities.lean CommandExecution.lean CreditUsage.lean \
  ExecutionTrace.lean ToolProvenance.lean Twin.lean Main.lean ProxyReport.lean \
  Proxy Protocol \
  --backend system --json > ../gokujo-report.json || status=$?
cat ../gokujo-report.json | head -40
rm -f gokujo-main.lean gokujo-main.c gokujo-temp
echo "== gate exit $status =="
exit "$status"
