# Task: Close the Full-Dir `gokujo check RequestProject` Gaps + Apply Aristotle Results

**Status:** done (2026-10-18)
**Project:** lean-worker
**Priority:** P1
**Branch:** `agent/fix-requestproject-check` (worktree `lean-worker-worktrees/fix-requestproject-check`)

## Description

Make full-dir `gokujo check RequestProject` an unqualified PASS (it had failed on
exactly 3 source-level modules), and adapt `~/projects/lean-worker` to carry the
results of the previous runs in `/mnt/data1/aristotle-results/` — per operator
direction: "read the last aristo results from previous runs and adapt our
~/projects/leanworker for it to apply them."

## The 3 original gaps and how each was closed

1. **`RequestProject/Main.lean` imported `Mathlib`** (unknown module prefix under
   the no-mathlib policy). Fixed in place: dropped `import Mathlib` and the
   Mathlib-only scoped opens (`BigOperators`, `Real`, `Pointwise`); kept core
   `Nat`/`Classical`.
2. **`RequestProject/ProxyReport.lean` imports `RequestProject.Proxy.Export`** —
   the whole `RequestProject/Protocol/` (5 files) and `RequestProject/Proxy/`
   (7 files) subtrees were missing. Applied from **aristo run `58ae717d`**
   (`output-final_aristotle`, self-export 2026-09-19) — the run that originally
   produced this tree. Both subtrees import only Lean core + each other.
3. **`RequestProject/PluginContexts/AllModules.lean` imports 36
   `RequestProject.PluginContexts.*` modules that existed only as top-level
   `minimal/*.lean`** (and those never compiled: Mathlib tactics without
   Mathlib). Materialized the 36 files under `RequestProject/PluginContexts/`
   and repaired them to compile on elan lean 4.28.0:
   - `norm_num [List.length]` → `decide`; Lean-3 `List.mem_of_mem_nth? (by omega)`
     → `decide`; `exFalso` "proofs" of false statements → honest true statements
     (`commands.length = 0` / `capabilities = []` where the data is empty —
     theorem renamed accordingly, e.g. `*_commands_nonempty` → `*_commands_empty`);
   - `aristotle_manager.lean`: invalid `Json.of { … }` blocks →
     `List (String × String)` (the `Json` field type was file-local), stray-dot
     typos fixed, Lean-3 `match … end` → Lean-4 `match`, `Some`/`None` →
     `some`/`none` (this elan build has no `Some`/`None` aliases), comma-`unfold`
     → space-separated, `Option.get` theorem restated;
   - **name-collision fix:** every plugin file declared `PluginContexts.PluginInterface`,
     so `AllModules` (which imports all 36) failed with "environment already
     contains …". Each file now opens `namespace PluginContexts.<mod>`.

## Aristotle results applied (run `749a6eb8`, 2026-10-18 15:19)

Applied the **no-mathlib, import-closed subset — 14 modules**:
`Analyzer`, `Classify`, `Chunks`, `Reflect`, `ReflectGraph`, `Demo`, `Synonyms`,
`ModuleDeps`, `Schema`, `Fingerprint`, `TrustPolynomial`, `TrustPolynomialSpec`,
`TrustCapsule`, `TrustCapsuleMeasured`.

Deliberately **excluded** (and why):
- `Mobius`, `Fitting`, `Ontology` — `public import Mathlib` (no-mathlib policy);
- `TrustCapsuleTest` — uses `native_decide` (fails gokujo's holes gate);
- `Tolerance`, `Introspection`, `SelfPartition`, `SelfApply`, `Experiments/*`,
  `Nesting` — import modules absent from the run export
  (`NoiseInstance`, `Experiments.PrivateCells`, `Experiments.C12`, `ChannelToy`,
  `GraphPass`, `Coherence`, `GeneralizeDemo`, `GraphPassReport`, `WriteBack`,
  `SelfMerge`, `Hexagon`, … — searched, not present in any run on this host);
- run `c3de2a2c` (`internal-final`, A11y/CDM) and `3a8443b1`/`10671d9f`
  (Tracker/LeanWorker/ProofChain trees) — different projects, no overlap with
  this repo's `RequestProject` namespace, not applied.

## Commands

```bash
cd /home/mdupont/2026/09-september/18/lean-worker-worktrees/fix-requestproject-check/minimal
./gokujo check RequestProject                      # the gate
lake -f fast-lakefile.toml build RequestProject    # flake.nix's build path
lake -f fast-lakefile.toml build RequestProject.PluginContexts RequestProject.Proxy RequestProject.Protocol
```

## Verification (receipts 2026-10-18, elan lean 4.28.0)

- `./gokujo check RequestProject` → **PASS, exit 0** (pipefail, real status:
  `EXIT=${PIPESTATUS[0]}`). Incremental: `37 built, 0 failed`; **clean rebuild
  after `rm -rf .lake/build`: `73 built, 0 cached, 0 failed` in 3m39s**.
- holes gate: `no sorry, no admit, no native_decide (992 declarations in 73 files)`;
- axioms gate: `audited 435 declarations; observed: propext, Quot.sound,
  Classical.choice` — nothing beyond the allowed set;
- `lake -f fast-lakefile.toml build RequestProject` → **exit 0** (37 jobs,
  2m52s); `lake -f fast-lakefile.toml build RequestProject.PluginContexts
  RequestProject.Proxy RequestProject.Protocol` → **exit 0** (17 jobs);
- `fast-lakefile.toml` parses (tomli) and its roots are now dotted module
  names for Proxy/Protocol (bare roots resolved to nonexistent top-level files),
  `Main`/`ProxyReport` rejoined, `PluginContexts` reduced to the single
  `AllModules` root;
- per-file compile of all 36 plugin contexts: 36/36 pass
  (`LEAN_PATH=.lake/build/lib/lean lean --root=. <file>`).

## Dependencies
- rebuild-fixed-binary task (gokujo binary)
- `/mnt/data1/aristotle-results/` runs 58ae717d and 749a6eb8

## Notes / limitations
- Top-level `minimal/*.lean` plugin files (the 36 originals) are **unchanged**
  and still don't compile standalone — they remain the `Minimal.PluginContexts`
  lib roots of the default `lakefile.toml`, which was out of scope here. The
  compiling copies are the `RequestProject/PluginContexts/` ones.
- `main`'s `.github/workflows/lean.yml` had an unrelated uncommitted edit in the
  primary checkout; untouched by this branch.
- Not pushed; no PR opened (local branch only).
