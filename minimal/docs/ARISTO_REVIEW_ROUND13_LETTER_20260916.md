# Round 13 audit letter (generated 2026-09-16T16:48:36Z, head `cd3ceac`): the model is axiom-clean, the schedule arithmetic reconciles, but the SLA cannot be signed off

**Inputs.** The letter itself, and the head it names. `cd3ceac` ("feat(server): wire tweet
archive store directly to bus subscription") is present in three uploaded bundles
(`tracker-20260916-main-35e3745`, `tracker-20260918-main-3b88232`,
`tracker-20260920-wip-commit-all-changes-…-9c195fd`). All source statements below are read from
that commit. The live edge-object JSON quoted in §2 of the letter appears in no uploaded file.
It is checked for internal consistency and against the code that produced it, not against an
independent capture.

**How the letter is produced.** It is written by
`scripts/prepare-aristotle-comprehensive-ask.ts` at `cd3ceac`. Only the JSON blocks and the five
gate transcripts are live. The following lines are fixed template text, printed whatever the
system does:

* the whole executive summary, including "34 active follower accounts", "229 placed edges",
  "P50 ~38 ms", "545 ms cadence, gcd(9,34)=1", "1,018 genuine tweets", "632 media", "16/16 …
  0 unmerged branches" and "Three-Stage Detection SLA (Proven Met)";
* both "**ONLINE**" lines;
* "~1,500 / 100,000" and "98.5 %" headroom;
* "100 % compliant, 0 semantic contradictions";
* the §4 Lean listing, including `liveSnapshotTweets : Nat := 1018`.

The script also runs `lean lean/RequestProject/Tracker/Gui2Lean4.lean`, but it never prints that
output into the letter.

**What is machine-checked here.** `RequestProject/Tracker/Review/Round13Letter20260916.lean`
contains 24 theorems. It has no `sorry` and uses only standard axioms. The whole project builds
(8 334 jobs).

---

## Action 1: audit of `Gui2Lean4.lean` — **zero custom axioms: confirmed; soundness: not established**

* **Axioms.** Re-elaborated here with `#print axioms`, both the `cd3ceac` text and the current
  text of the module use `propext` at most. Eight of the eleven theorems use no axiom at all. The
  file contains no `axiom`, `sorry`, `native_decide` or `implemented_by`.
* **The letter's §4 does not match the source.** At `cd3ceac` the file says
  `liveSnapshotTweets : Nat := 1003`, not 1 018. 1 003 also matches none of the four archive
  counts in the letter: 1 018, 250, 3 546 and 3 544 (`snapshot_tweets_match_no_archive`).
  `live_empirical_gui_soundness` proves `1003 ≥ 1000 ∧ 229 ≤ 3292 ∧ 604 < 1000` about those
  hand-entered constants, so it says nothing about the deployment.
* **The other theorems restate their hypotheses.**
  * `zero_drop_invariant` is `h → h`.
  * `universal_hot_tier_conservation` is `1646 = 1646 + 0` after substitution.
  * `fleet_follow_capacity_bounded` is `3292 ≤ 34 * 400`.
  * `landmark_coverage_sound` is `true && true && true = true`.

  None of them reads a captured value.
* **The predicates are weaker than their descriptions.**
  * `isA11yCompliant` reads the Boolean `hasAccessibleLabel`, never `accessibleName`. An
    interactive control with the empty string as its name is "compliant"
    (`empty_name_is_compliant`), so theorem 1's gloss ("all interactive elements require
    non-empty labels") is not what it proves.
  * `isLatencySemanticsHonest` uses a 1 000 ms threshold, not the 500 ms SLA. A 604 ms p50
    marked "subsecond" passes as honest (`honest_latency_can_miss_the_sla`).
  * The same predicate calls the edge object's actual 359 ms p50 dishonest if it is shown
    without a subsecond badge (`underclaim_is_dishonest`).

## Action 2: reconciliation of the edge-object state with the timing arithmetic — **holds for the grid; the "545 ms cadence" does not**

These checks use `schedule.mjs` at `cd3ceac` (`offset(k) = ⌊k·d/M⌋`, d = 10 000, M = 11 × 10 = 110).

| field in letter | value | recomputed | theorem |
|---|---|---|---|
| totalSlots / startsPerMinute | 110 | 11 × 10 | `derived_fields_reproduce` |
| firstOffsetMs / lastOffsetMs | 0 / 9 909 | ⌊0⌋ / ⌊109·10000/110⌋ | same |
| minGapMs / maxGapMs | 90 / 91 | every gap is 90 or 91; both occur | `gaps_are_90_or_91` |
| derivedToleranceMs | 90 | min(100, ⌊9999/110⌋) | `derived_fields_reproduce` |
| strictSeparationToleranceMs | 89 | ⌊10000/110⌋ − 1 | same |
| latestAdmittedStartMs | 9 999 | 9 909 + 90 | same |
| quotaWorstCasePerReader | 165 | 15 × 11; fits within 180 − 10 | same |
| validation warning | tolerance 90 can coincide with the next slot | true: every late start stays inside the 10 s burst, one coincides at 90, all are strict at 89 | `tolerance_warning_is_correct` |

These numbers do **not** describe a 545 ms cadence.
* The 110 starts fill the first 9 909 ms of each minute. The gap across the minute boundary is
  50 091 ms (`minute_boundary_gap`).
* Each reader's own starts are 909 or 910 ms apart inside the burst (`per_reader_gaps`).
* 545 ms is 60 000 / 110, a cadence the deployed `minute_burst` mode does not run.

**Quota.** The configured grid plans 110 × 1 440 = 158 400 starts a day. That is above the
100 000 free-tier figure the letter uses. "~1 500 a day" is under 1 % of the plan
(`quota_line_needs_idling`). The 98.5 % headroom therefore holds only while the scheduler runs
under one hundredth of its configuration. In any case, that line is template text.

## Action 3: hot tier and 2× redundancy "under gcd(9, 34) = 1" — **redundancy holds per the ledger counts; coprimality is not the reason; hot tier is not evidenced**

* `gcd 9 34 = 1` is true (`gcd_nine_thirtyfour`). What it gives is a single 34-cycle: the
  multiples of 9 cover every residue mod 34 (`stride_nine_full_tour`).
* **2× redundancy follows from the bucket counts alone.** The buckets close on the watchlist
  (0 + 0 + 510 + 1 136 = 1 646, `buckets_close`). With the zero and one buckets empty, every
  target has at least two ledger entries (`two_x_from_buckets`).
* **Coprimality is not needed for redundancy.** In the "primary *a*, secondary (*a* + off) mod
  *N*" assignment, the two followers differ whenever *N* ∤ off
  (`distinct_followers_of_nonzero_offset`). Offset 17 with 34 accounts has gcd 17 and still
  works (`redundancy_without_coprimality`).
* **9 and 34 do not appear in the shipped code.**
  * The pair appears only as a literal evidence string in `audit-three-stage-pipeline.ts` and in
    the letter template.
  * The partitioner `follow-split.mjs` uses 81 accounts with offset 40.
  * The edge worker picks targets with step 15 over 1 646.
  * The live fleet is 85 accounts.
* **What the ledger counts mean.** A "placed edge" in the edge object is an entry in a
  `follow_ledgers[*].followed` list. `worker.mjs` appends to that list on HTTP 200, and also on
  "already requested", "User not found", "Cannot find specified user" and "blocked from
  following". `POST /api/schedule/follows/record` can also overwrite the list. 5 365 is
  therefore an upper bound on follows actually in place, not a measurement of them.
* **The follow figures disagree.** The letter text and the Lean snapshot say 229, the
  three-stage prover (local server) says 496, and the edge object says 5 365. The bijection test
  covers 13 accounts, which cannot carry 5 365 edges at the 400 cap (`follow_counts_disagree`).
* **`redundantPct: 31` is the share with *exactly* two entries** (510 / 1 646). The share with at
  least two is 100 % (`redundant_pct_is_exactly_two_share`).
* **Hot tier.** The edge-object JSON carries no tier field, and coprimality has no bearing on
  tiers. The only formal "proof" is `universal_hot_tier_conservation`, which proves 1 646 =
  1 646 + 0. The round-13 package reviewed earlier (`docs/REVIEW_ROUND13.md`) showed that the
  sweeper's `shards-1500.json` sweeps 150 accounts hot and 1 496 cold. Nothing in this letter
  revisits that.

## Action 4: SLA sign-off — **declined for Stage 1**

**Stage 1 (push, < 500 ms).**
* The letter's own prover transcript reports **FAIL** at 2 000 ms p50. The prover at `cd3ceac`
  no longer falls back to literals, so this is a real reading of the local server.
* In the edge object, push-sourced detections are 13 of 250 (5.2 %); the source counts close,
  13 + 231 + 6 + 0 = 250 (`sources_close`).
* Their median is 359 ms. Their smallest sample is 208 ms, so no push detection is at or near the
  "~38 ms" headline (`no_push_sample_at_38`).
* The push p90 sits at index 11 of 13 (`percentile_indices`) and reads 649 ms, so at least 2 of
  the 13 push detections exceed 500 ms (`push_pool_misses_500`).
* `worker.mjs` takes min, avg, p50 and p90 from the push pool, but p95, p99 and max from all 250
  samples. On that whole pool, at least 13 detections exceed 500 ms (`whole_pool_misses_500`) and
  at least 3 took 18 s or more (`whole_pool_has_18s_tail`). The maximum is 55.7 s.
* `p50DetectMs = p50PushDetectMs = 359` is equal by construction, not by coincidence.
* `p50PollLagMs = 543` is the median over all 250 samples, push samples included.

**Stage 2.** The grid arithmetic is correct and the quota per 15-minute window fits. The "zero
drop" label is not established. The rendered KPI `"pushVsPoll": "100% Zero Drop"` is a string,
and `zero_drop_invariant` is `h → h`. The prover passes Stage 2 on `startsPerMinute === 110`
alone.

**Stage 3.** The archive exists. The three counts in the evidence (250 at the edge, 3 546 /
3 544 locally, 1 018 in the text) describe different stores. The "PASS" rules are
`count > 0`.

**Accessibility.**
* "100 % compliant, 0 semantic contradictions" is template text.
* The rendered tree's own `liveHydratedKpis` read `"–"` / `null` for tweets, media, latency,
  follows and accounts. The capture therefore holds no hydrated values whose honesty could be
  judged.
* The node counts in the letter disagree: 1 667 / 739 in §3 against 323 in the catalog.

**Branches.** "16/16 … 0 unmerged" is template text. The letter's own audit lists
`feat/client-error-and-spot-check-modals` (`cbc2642`) as unmerged, and it is not an ancestor
of `cd3ceac` (2 commits ahead). Seven `origin/*` refs sit at `337afef`, 11 commits behind.

## Verdict

| # | Requested action | Result |
|---|---|---|
| 1 | Zero custom axioms in `Gui2Lean4.lean` | **Confirmed.** Its theorems are restatements of their hypotheses or facts about hand-entered constants, and its compliance predicate ignores the accessible name |
| 2 | Edge state ↔ timing arithmetic | **Reconciles field-for-field**, including the warning; the advertised 545 ms cadence does not exist in `minute_burst` mode |
| 3 | Hot tier and 2× redundancy under gcd(9,34)=1 | **2× holds of the ledger counts** (upper bound on real follows); it needs only off mod N ≠ 0, not coprimality; hot tier not evidenced |
| 4 | Sign off on customer SLA | **Not signed off.** Stage 1 fails by the letter's own prover and by the edge object's own push percentiles |
