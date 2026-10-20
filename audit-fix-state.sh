#!/usr/bin/env bash
# audit-fix-state.sh — check every lean-worker checkout for PR#25 vuln vs fix state
# Vulnerable worker sha (audit PSI-U): f711e692e74afd89e4e906636dff5ee22552209f6076e1aa271d1a37e8cf5aab
# Gokujo fix marker: scanStrTR (tail-recursive lexer, commit 434c4da)
set -u
JSON="$HOME/projects/lean-worker/locate-lean-worker-classified.json"
VULN_SHA=f711e692e74afd89e4e906636dff5ee22552209f6076e1aa271d1a37e8cf5aab
printf '%-52s %-28s %-10s %-9s %-9s %s\n' CHECKOUT BRANCH WORKER PROVEGOAL GOKUJO NOTES
jq -r '.checkouts[]' "$JSON" | sort -u | while read -r d; do
  [ -d "$d" ] || continue
  case "$d" in *.lake/packages*) continue;; esac
  br=$(git -C "$d" rev-parse --abbrev-ref HEAD 2>/dev/null || echo "-")
  # worker: find first bone-worker.mjs (prefer minimal/scripts, skip .lake)
  bw=$(find "$d" -maxdepth 4 -name bone-worker.mjs -not -path '*/.lake/*' 2>/dev/null | head -1)
  wstate="-"; pstate="-"; note=""
  if [ -n "$bw" ]; then
    h=$(sha256sum "$bw" | cut -d' ' -f1)
    if [ "$h" = "$VULN_SHA" ]; then wstate="VULN-PSIU"; else wstate="DIFF"; fi
    # proveGoal reads outside comment lines
    if grep -v '^\s*//' "$bw" | grep -q 'proveGoal'; then pstate="READ"; else pstate="comment-only"; fi
    grep -q "gokujo check exit 0" "$bw" && note="exit0=proved"
  fi
  # gokujo: find Gokujo.lean, check for scanStrTR
  gj=$(find "$d" -maxdepth 4 -name 'Gokujo.lean' -not -path '*/.lake/*' 2>/dev/null | head -1)
  gstate="-"
  if [ -n "$gj" ]; then
    grep -q 'scanStrTR' "$gj" && gstate="FIXED" || gstate="recursive"
  fi
  # remediation artifacts
  find "$d" -maxdepth 4 \( -iname '*job-verifier*' -o -iname '*attest*' \) -not -path '*/.lake/*' 2>/dev/null | grep -q . && note="$note verifier-artifact"
  printf '%-52s %-28s %-10s %-9s %-9s %s\n' "${d#$HOME/}" "$br" "$wstate" "$pstate" "$gstate" "$note"
done
