# Review: gui2proof go-live launch-dialog guard, 2026-10-18

Inputs reviewed: `gui2proof-golive.json` (sha256 `101e19a3…ad48`) and
`Gui2ProofGolive.lean` (sha256 `cf607cfb…52c2`), both at the project root.
The branch `buffy/golive-ladder-20261016` / commit `1b89347b` is **not** in any
uploaded bundle (the newest bundle is `tracker-20260930-…-d54d5c8b`), so
`scripts/gui2proof-golive.ts`, `scripts/golive-launch-dialog.mjs` and
`lean/lean-toolchain` could not be read. Everything below is from the two text
artifacts. Claims about the generator are inferred from those artifacts.

Machine-checked support: `RequestProject/Tracker/Review/Gui2ProofGolive20261018.lean`
(builds, no `sorry`, axioms at most `propext`).

Compilation reproduced: `lake env lean Gui2ProofGolive.lean` with Lean
v4.28.0 gives 0 errors and 0 warnings, and `checks.length = 16`.
`#print axioms launch_dialog_safe` reports **no axioms at all**.

## Complaints, worst first

### A. Fail-closed chain (task item 3)

1. **The fail-closed chain can be bypassed by omission. A skipped or failed check can still produce a compiling artifact that claims success.**
   - The gate is `checks.all (· == pass)` over whatever list the generator emits.
   - `omitting_checks_preserves_pass` proves that removing any checks preserves a pass.
   - `failed_check_erased_still_passes` gives a concrete case: append a `fail` and the gate rejects, but drop it and the gate passes.
   - This round's own handling of the skipped live-deploy checks is exactly that bypass: they are dropped from the list rather than emitted as `skipped`.
   - So the compiler gate can only reject verdicts the generator chose to write. The kernel guarantees nothing about completeness. Whether a *failed* guard check is emitted as `Verdict.fail` or silently dropped depends entirely on generator code that was not supplied.
2. **The gate accepts an empty list.** `empty_list_passes_gate`: `[].all _ = true`. If the generator emits zero checks (for example after a crash, a bad JSON path, or a filter bug), the theorem `launch_dialog_safe` still compiles. The artifact pins neither a required id set nor a length.
3. **`checkCount := 16` and `skippedCount := 0` are bare literals, not tied to anything.**
   - No theorem says `checks.length = checkCount`.
   - Over the evidence, `skippedCount` is wrong: the run recorded 2 skipped checks (`artifact_skippedCount_contradicts_evidence`).
   - The reading "0 skipped *in the guard*" is not stated anywhere.
   - This is the same hard-coded-number pattern as earlier rounds.
4. **The artifact records no trace that live deploy was skipped.** Leaving the theorem out is honest about what was proved. But the `.lean` contains no `liveDeploy` list, no `enabled = false` and no skipped entry. A reader of the artifact cannot tell "the live deploy was refused" from "live deploy is not part of this guard". The docstring's "a single failed OR skipped check makes this FALSE" is untrue of this file as emitted: two checks were skipped and the file compiles.
5. **Over the full evidence, the artifact's own predicate is false.** `full_evidence_fails_gate`: on all 18 recorded checks, `allPassed = false`. "16/16" is a denominator chosen after excluding the skips. The honest headline is "16 pass, 2 skipped, of 18", the same counting complaint as 22-vs-20.
6. **The gate can only fail at the verdict tag.** `Check` has only `id` and `verdict`, and `gate_ignores_ids` shows even the ids are irrelevant. The evidence strings never reach the `.lean`, so a pass with empty or vacuous evidence produces an identical artifact. The theorem is `decide` over literals the generator wrote. It proves that the generator wrote `pass` 16 times and nothing about the dialog.
7. **Nothing binds the artifact to the evidence or to the run.**
   - The `.lean` has no `generatedAt`, no commit, no hash of the JSON and no base URL.
   - The JSON has no commit, no branch and no hash of the `.lean`.
   - The `.lean` cites `data/gui2proof-golive.json`, but the evidence was attached as a root-level file. Nothing shows they are the same run.
   - The docstring claims the checks held "on a live run", but nothing in the file can be checked against that.

### B. `.lean` vs evidence (task item 2)

8. **The axiom claim is inaccurate.** It is stated as "standard axioms only (propext, Classical.choice, Quot.sound)", but the theorem uses no axioms. That is harmless, but the stated property was not what was checked.
9. **These items match:** 16 ids, in the same order and with the same verdicts as `guard.checks`; one theorem; no `sorry`; no `axiom`. The live-deploy theorem is absent, not weakened. Any weakening it could have had is already covered by items 1–5.
10. **I could not check the toolchain claim.** The repo here pins `leanprover/lean4:v4.28.0` at the root. `lean/lean-toolchain` is not in any upload. The artifact also has no `import`, so "compiled by the pinned toolchain" would pass under almost any Lean 4 version. The pin adds no assurance.

### C. Guard evidence (task item 1)

11. **Refusal checks have no positive control. A server that rejects everything passes all five.**
    - `deploy_requires_confirm`, `preview_requires_credential_and_name`, `delete_requires_confirm` and `verify_requires_url` record only `HTTP 400`.
    - `deploy_refuses_unknown_credential` records only `HTTP 404`.
    - No response body, no error code and no proof that wrangler was not spawned are recorded.
    - With live deploy skipped, no request was ever *accepted*, so "refused for the right reason" is untested.
12. **`deploy_refuses_unknown_credential` = HTTP 404 can't be told apart from "route not found".** A missing or renamed `/api/deploy` route passes this check.
13. **`launch_log_carries_no_creds` may pass vacuously.** The evidence reads "history entries scanned", with no count, byte size or file existence. With no deploy performed, the log may be empty or missing. There is no presence check pairing it.
14. **`login_url_never_carries_api_token` is vacuous for its positive half.** The claim is "embeds the bootstrap key". The evidence is "node/history surfaces carry no api token", with no login URL examined and no node count. With no deploy, there are probably no nodes, and no bootstrap key was ever observed.
15. **`temp_config_cleaned_up` is vacuous.** "No temp configs on disk" holds if refusals happen before any temp file is written, or if the worker directory path is wrong. Neither the directory nor a before/after listing is recorded, and nothing shows a `.launch-*.toml` is ever created on any path.
16. **There is no check for the static HTML.** The scope claims absence from "static HTML, JSON APIs, hydrated DOM, launch log". `gui_served` records only a size (27914 bytes) and no token scan. The hydrated-DOM scan (31529 bytes) arguably covers it, but there is no separate result for it.
17. **None of the token-absence scans prove the needle was loaded.**
    - No token length or fingerprint is recorded for the string searched for.
    - If decrypting the secret failed and the needle were a placeholder, "0 occurrences" would still pass.
    - The JSON says the "real Cloudflare api token" (singular), while there are 3 credentials, each with `hasToken`. It is not stated whether one token or three were searched.
    - The prompt says "sops token" and the evidence says "Cloudflare api token", which is also not reconciled.
18. **`no_credential_token_in_api`: "scanned 3 endpoints"** does not name the endpoints, so coverage of "every JSON API" can't be checked.
19. **`gui_hydrates_credential_rows` is a weak presence pair.** "credential name(s) rendered" gives no count. One of the 3 names would pass. The pairing exists, but it doesn't show the rows that could leak were rendered.
20. **`credentials_only_fetched_by_gui` evidence doesn't match its claim.** The claim is "only the dialog's own credential API". The evidence, "4 request(s), all same-origin", shows only same-origin.
21. **`server_loopback_only`** does not name the 2 interfaces or say whether IPv6 was tested. "Closed" doesn't say whether that was connection-refused or a timeout. `health_public_liveness` is the matching presence probe, which is fine, but the "public" in its name contradicts loopback-only wording.
22. **`guard.allPassed: true` is the only top-level boolean.** The JSON has no overall verdict, so a consumer reading `guard.allPassed` sees success for a run with skipped checks.

### D. Previous complaints — twitterstorm round d71fd135

Nothing in this submission touches the twitterstorm dashboard or prover code, and the commit is not available. Each item is **still open** (not shown addressed). Where the same defect recurs here, that is noted.

23. Watchlist-size `0`-on-error stub: **still open.** It recurs in spirit: absence scans report 0 with no proof that the scan ran (items 13, 17).
24. `zero_hard_coded_values` proving `0 = 0`: **still open.** It recurs: `launch_dialog_safe` is `decide` over generator-written literals (item 6), and `skippedCount := 0` is a literal (item 3).
25. `allProven` being a definition: **still open.** It recurs partially: `allPassed` is again a `def`. A theorem now asserts it, but only over the emitted list (items 1, 2).
26. 22-checks-vs-20 counting: **still open.** It recurs as 16 vs 18 (item 5).
27. ±50% "live" tolerance (69 vs 114 accepted): **still open.** Not exercised here.
28. 0-vs-0 comparisons indistinguishable from hard-coded zeros: **still open.** It recurs: "0 occurrences" with no needle fingerprint (item 17).
29. `kpiLatencySub` empty state counted live: **still open.** It recurs as vacuous passes on empty state (items 13–15).

### E. Previous complaints — main round 142d703c (Round 13)

Nothing in this submission addresses these items. All are **still open**:

30. Push-detection SLA declined (359 ms median vs 500 ms claim; prover FAIL at 2000 ms): **still open.**
31. Gui2Lean4 theorems restating assumptions: **still open.** It recurs: the new artifact's single theorem is again a restatement of emitted data (item 6).
32. Accessibility check accepting empty accessible names: **still open.**
33. "Honest latency" using 1000 ms rather than the 500 ms SLA: **still open.**
34. Missing 545 ms cadence: **still open.**
35. Three disagreeing follow counts (229/496/5365): **still open.**
36. Wrong "16/16 merged" claim: **still open.** Note that this round's own headline "16/16" repeats the selective-denominator pattern (item 5).

## What would close items 1–7

- Emit **every** check, including `skipped` ones, into the `.lean`.
- Pin the expected id list in a hand-written (non-generated) file, and prove `checks.map (·.id) = expectedIds`.
- Derive `checkCount` and `skippedCount` by `List.length`/`filter`, not literals.
- Make the live-deploy theorem a *separate* statement that would be emitted and fail when its checks are skipped. Alternatively, gate on `guard.allPassed && (liveDeploy.enabled → liveDeploy.allPassed)` and record `enabled = false` in the file.
- Embed the JSON's sha256 and the commit in the `.lean`.
