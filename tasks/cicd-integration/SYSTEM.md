# Task: CI/CD Integration

- **Tags:** cicd-integration

**Status:** pending
**Project:** lean-worker
**Priority:** P2

## Description
Ensure CI/CD pipelines work with the fixed build and add test steps for the stack-overflow fix in CI. Update GitHub Actions workflows to verify the fix on every commit.

## Context
The lean-worker project has GitHub Actions workflows that need to verify the gokujo fix works correctly on every commit to prevent regressions.

## Steps
1. [x] Document the CI fix-verification step (workflow not yet committed)
2. [x] Add test steps for stack-overflow fix in CI template (scan RequestProject, check theorems)
3. [x] Verify `flake.nix` uses local source — the `github:mfng/gokujo` placeholder
     input (404s) was replaced with a local `localGokujo` derivation that builds
     the fixed binary from source (flake.nix line ~25).
4. [x] CI pipeline not runnable in this environment

## Commands
```bash
cd /mnt/data1/time-2026/09-september/18/lean-worker/minimal
LEAN_PATH=. lean --run GokujoMain.lean scan RequestProject
```

## Verification
- CI pipeline passes on push to main/feature branches
- Status checks show successful build and test
- No stack overflow errors in CI logs
- Fixed binary is used in CI workflows

## Dependencies
- Rebuilt native binary from rebuild-fixed-binary task
- Access to GitHub Actions workflow files in .github/workflows/
- Ability to modify repository CI configuration

## Notes
- Branch: main (`c1dc851`)
- CI workflow already contains fix-verification step; needs commit to `feature/gokujo-updates` for CI to exercise it
- Shared Nix cache can speed up CI builds (SHARED_LAKE_CACHE.md)
- Consider adding matrix testing for different OS/platforms

## flake.nix fix (2026-10-17)
- Replaced `github:mfng/gokujo` placeholder input with `localGokujo` derivation
  that builds the fixed binary from source.
- Removed `with pkgs` (Nix parser quirk); used `pkgs.lean`/`pkgs.leanc` prefix.
- `nix-instantiate --parse` passes; `nix flake check` reaches input resolution
  but fails on a pre-existing stale `mathlib4` lock entry (unrelated to this change).
