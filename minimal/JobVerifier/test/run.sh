#!/usr/bin/env bash
# RT-9 regression suite: every v-case must be REJECTED with its reason code;
# every c-case must be ACCEPTED.  Demonstrates the checker closes the
# scanner-bypass class as a class, not per-instance.  The r-cases exercise
# refless mode (no reference statement): acceptance decided from the
# elaborated environment alone — the mode bone-worker uses when an offer
# carries no refGoal coordinates.
set -uo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"          # minimal/JobVerifier/test
MINIMAL="$(cd "$HERE/../.." && pwd)"
DRIVER="$MINIMAL/scripts/job-verifier.sh"

declare -A EXPECT=(
  [c0-honest]="OK:0"
  [v1-sorry]="SORRY:1"
  [v2-private-axiom]="TARGET_MISSING:1"
  [v3-nested-comment]="SORRY:1"
  [v4-mismatch]="STATEMENT_MISMATCH:1"
  [v5-missing]="TARGET_MISSING:1"
  [c3-cheat-axiom]="AXIOM_NOT_ALLOWED:1"
  [v6-notlean]="NOT_LEAN_SOURCE:1"
)

pass=0; fail=0
for c in "${!EXPECT[@]}"; do
  want_reason="${EXPECT[$c]%%:*}"; want_rc="${EXPECT[$c]##*:}"
  src="$HERE/cases/$c/A.lean"
  [[ -f "$src" ]] || src="$HERE/cases/$c/A.txt"
  out="$("$DRIVER" "$src" A t Ref __expected 2>/dev/null)" ; rc=$?
  got_reason="$(grep -o '"reasonCode":"[^"]*"' <<<"$out" | cut -d'"' -f4)"
  if [[ "$got_reason" == "$want_reason" && "$rc" == "$want_rc" ]]; then
    printf 'PASS %-18s rc=%s %s\n' "$c" "$rc" "$out"
    pass=$((pass+1))
  else
    printf 'FAIL %-18s want=%s/%s got=%s/%s\n' "$c" "$want_reason" "$want_rc" "$got_reason" "$rc"
    fail=$((fail+1))
  fi
done
echo "-----"
echo "pass=$pass fail=$fail"

# Refless mode (3-arg form, no reference): same expectations as full mode
# for the environment-based reason codes.  v4-mismatch is skipped —
# STATEMENT_MISMATCH needs a reference by definition.
declare -A EXPECT_REFLESS=(
  [c0-honest]="OK:0"
  [v1-sorry]="SORRY:1"
  [v2-private-axiom]="TARGET_MISSING:1"
  [v3-nested-comment]="SORRY:1"
  [v5-missing]="TARGET_MISSING:1"
  [c3-cheat-axiom]="AXIOM_NOT_ALLOWED:1"
  [v6-notlean]="NOT_LEAN_SOURCE:1"
)

echo "----- refless -----"
rpass=0; rfail=0
for c in "${!EXPECT_REFLESS[@]}"; do
  want_reason="${EXPECT_REFLESS[$c]%%:*}"; want_rc="${EXPECT_REFLESS[$c]##*:}"
  src="$HERE/cases/$c/A.lean"
  [[ -f "$src" ]] || src="$HERE/cases/$c/A.txt"
  out="$("$DRIVER" "$src" A t 2>/dev/null)" ; rc=$?
  got_reason="$(grep -o '"reasonCode":"[^"]*"' <<<"$out" | cut -d'"' -f4)"
  if [[ "$got_reason" == "$want_reason" && "$rc" == "$want_rc" ]]; then
    printf 'PASS %-18s rc=%s %s\n' "$c" "$rc" "$out"
    rpass=$((rpass+1))
  else
    printf 'FAIL %-18s want=%s/%s got=%s/%s\n' "$c" "$want_reason" "$want_rc" "$got_reason" "$rc"
    rfail=$((rfail+1))
  fi
done
echo "-----"
echo "full pass=$pass fail=$fail | refless pass=$rpass fail=$rfail"
[[ $fail -eq 0 && $rfail -eq 0 ]]
[[ $fail -eq 0 ]]
