# Task: Rebuild Fixed Native Binary

**Status:** done (2026-10-18)
**Project:** lean-worker
**Priority:** P1

## Description
Rebuild the native `gokujo` binary using the fixed source code with iterative `walkLean` and `scanStrTR` implementations to resolve stack overflow issues when scanning large projects like Solfunmeme (663 files).

## Context
- Fixed iterative `walkLean`: Located in `Gokujo.lean` at lines ~1345 in the `lean-worker/minimal` directory ✓
- Fixed iterative `scanStr`: Added `scanStrTR` as iterative alternative to recursive `scanStr` ✓
- Proof Equivalence: `@[csimp] theorem scanStr_eq_scanStrTR` proves equivalence ✓
- Problem: Native binary `gokujo` predates the fix, compiled from older source

## Steps
1. [x] Rebuild native `gokujo` binary using the fixed source — via `nix build .#gokujo`
     once flake.nix's build recipe was fixed (`ad61696`: `lean --make` left the
     Lean 4 CLI, `-o` writes an `.olean`, and the entry-point shim imported a
     module from the wrong tree). Per operator direction 2026-10-18, the nix
     lane uses nixpkgs' lean (4.34.1) — no elan v4.28.0 for now.
2. [x] Verify the rebuilt binary has the iterative `walkLean` implementation —
     `strings result/bin/gokujo` shows `scanStrTR`/`walkLean` (8 hits), and the
     behavioural comparison below is consistent with the iterative code paths
     (~3x lower CPU on identical corpora).
3. [x] Compare with existing `minimal/gokujo` (pre-fix) binary — both binaries
     produce byte-identical scan results; the rebuilt one is ~3x faster in CPU.
     See receipts.

## Commands
```bash
cd /home/mdupont/projects/lean-worker
nix build .#gokujo          # the flake lane that now works
./result/bin/gokujo help    # runs: 极上 gokujo 1.0.0
```

## Verification (receipts 2026-10-18)
- `./result/bin/gokujo scan RequestProject` → exit 0, `11 files, 286
  declarations, 0 with holes`, no stack overflow (0.02 s).
- `./result/bin/gokujo check` on the 7 buildable core modules (Agent … Twin),
  with the nix lean 4.34.1 on PATH → **PASS**, exit 0: `0 built, 7 cached, 0
  failed`, `no sorry, no admit, no native_decide (284 declarations in 7 files)`,
  axioms audited (89 declarations; observed only propext, Quot.sound,
  Classical.choice).
- Full-dir `check RequestProject` failed then on exactly 3 modules, all source-level gaps:
  `Main` (imports `Mathlib` under the no-mathlib policy), `ProxyReport` (imports
  `RequestProject.Proxy.Export`, subtree absent), `PluginContexts.AllModules` (imports 48
  `RequestProject.PluginContexts.*` modules that exist only at top level).
  **Closed 2026-10-18** on branch `agent/fix-requestproject-check` — full-dir check is now an
  unqualified PASS (73 files, 992 declarations, clean rebuild): Protocol/Proxy subtrees applied
  from aristo run 58ae717d, Mathlib import dropped from Main, the 36 plugin contexts materialized
  and repaired under `RequestProject/PluginContexts/`. Receipts in
  `tasks/fix-requestproject-full-check/SYSTEM.md`.
- Large corpora, old vs rebuilt binary (identical results both sides, no
  overflow by either): tracker `lean/` 398 files scanned / 12,769 declarations
  — rebuilt 0.94 s real / 1.95 s user vs pre-fix 3.11 s real / 6.27 s user
  (~3x CPU); this repo's full tree 1,765 files / 32,752 declarations / 577
  with holes — rebuilt 4.96 s vs pre-fix 6.35 s.
- The original Solfunmeme (663 files) overflow repro cannot be rerun here:
  `/mnt/data1/git/github.com/solfunmeme` is an empty directory on this host.

## Dependencies
- Fixed Gokujo.lean source (already in minimal/)
- flake.nix updated to use local source (done; build recipe fixed in `ad61696`)

## Notes
- Branch: integration/vaciu-merge (flake fix `ad61696`)
- Verified fix works locally with `LEAN_PATH=. lean --run GokujoMain.lean scan RequestProject`
