# Rebuild Fixed Native Binary

This task covers rebuilding the native `gokujo` binary from the fixed source.

## Fixed Code

- `Gokujo.lean` — iterative `walkLean` (replaces recursive traversal)
- `scanStrTR` — iterative `scanStr` alternative
- `scanStr_eq_scanStrTR` — proof of equivalence

## Verification

- `./gokujo-fixed scan RequestProject` — completes without stack overflow
- `./gokujo-fixed check RequestProject` — passes with 0 holes
