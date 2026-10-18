# Aristotle results applied — round 2026-10-18

Date: 2026-10-18 · Applied by: Buffy · Repo: lean-worker @ `integration/vaciu-merge`

## Where these results came from

Dual-submit round of 2026-10-18 (tracker branch `buffy/golive-ladder-20261016`):
the gui2proof guard evidence (`gui2proof-golive.json`, 16/16) and the emitted
`Gui2ProofGolive.lean` were submitted text-only to both Aristotle accounts.

- **main `01057110`** — COMPLETE_WITH_ERRORS: **36 complaints**. Full list
  vendored at `docs/ARISTO_REVIEW_GUI2PROOF_GOLIVE_20261018.md`; the review's
  own machine-checked counter-theorems vendored verbatim as
  `ReviewGui2ProofGolive20261018.lean` (compiles clean, no `sorry`, axioms at
  most `propext`).
- **twitterstorm `cafdd57e`** — COMPLETE (ingested same day): **20
  complaints**, worst first: (1–2) a stale guard artifact survives an aborted
  run — the old `.lean` is never deleted first, so a crash leaves a stale
  `launch_dialog_safe` (and, after one opt-in run, a stale
  `launch_dialog_deploy_verified`) still compiling on disk; (3) token-absence
  checks reduce to a regex when no token is loaded; (4) `confirm` is a
  client-supplied JSON field — no Origin/Host/Content-Type check, so a
  cross-site POST can deploy or delete; (5) `/api/nodes/bootstrap` mutates
  the live account with no confirm; (12) **the compile gate accepts `sorry`**
  (`lean` exits 0 — no `#print axioms` step runs); (8) the negative probes
  would be DESTRUCTIVE if the guard under test had regressed (real-credential
  deploy probe); (19) unescaped values in the wrangler config and bootstrap
  `sh -c`; (20) opt-in mode accepts a 401-everything worker and never deletes
  it. Its Lean module `Gui2ProofGoliveReview.lean` proves the 16 ids/counts/
  skips facts for the artifact, and marks `allProven`-as-definition
  **addressed** there. Note (12) applies to ANY gui2proof pipeline including
  ours: a compile-only gate is not a no-sorry gate — both modules in this
  wave were therefore grepped for `sorry` AND compiled.
- Previous runs' complaints (main `142d703c` Round 13, twitterstorm
  `d71fd135` provenance round) are vendored as
  `docs/ARISTO_REVIEW_ROUND13_LETTER_20260916.md` and summarised in section
  D/E of the 2026-10-18 review — all still open.

## What the review proved (worst first)

1. The fail-closed chain is bypassable BY OMISSION — dropping checks preserves
   the gate's pass; an empty check list also passes.
2. `checkCount := 16` / `skippedCount := 0` were typed-in literals, and
   `skippedCount` contradicts the evidence (2 skipped).
3. The `.lean` bound nothing: no hash, no commit, no timestamp linking it to
   the JSON evidence or the run.
4. The `16/16` headline is a denominator trick over 18 recorded checks.
5. Refusal checks had no positive control; absence scans never prove the
   needle loaded; several checks pass vacuously on empty state.

## How this repo applied it

`Gui2ProofHardened20261018.lean` implements the review's own "What would close
items 1–7" recipe as a hardened gate and re-proves the review's bypasses as
REGRESSION theorems against it:

- `empty_list_now_fails`, `omission_now_fails` — the pinned id list kills both
  bypasses the review proved.
- `skipped_not_hidden` — skipped live-deploy checks are inside the gate's view.
- `derived_counts` — 18 checks / 2 skipped, derived by `List.length`/`filter`.
- `disabled_never_success` — a disabled live deploy reports
  `guardedNotExercised`, never plain success.
- `ids_now_matter` — renaming ids breaks the pin (the gate no longer ignores
  them).
- `exercuted_and_green_is_success` — the honest success path stays reachable.

Task record: `tasks/agent-b-wave-XIII.json`. Both modules compile clean on the
repo's pinned Lean 4.28.0 (the same version the reviewer compiled with).

## Still open (carried, not forgotten)

Round 13 items 30–36 of the 2026-10-18 review: push-detection SLA declined
(359 ms median vs 500 ms claim), theorems restating assumptions, empty-name
accessibility pass, 1000 ms "honest latency" threshold, missing 545 ms
cadence, the 229/496/5365 follow-count disagreement, and the wrong
"16/16 merged" claim — plus the d71fd135 items (watchlist `0`-on-error stub,
`0 = 0` theorems, ±50% tolerance, 0-vs-0 comparisons, empty-state "live").
