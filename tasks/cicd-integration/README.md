# CI/CD Integration

CI/CD pipeline configuration for the lean-worker project.

## Key Files

- `.github/workflows/lean.yml` — Lean build + CI gate
- `flake.nix` — Nix build with local source fix

## Verification Commands

```bash
cd /home/mdupont/projects/lean-worker/minimal
LEAN_PATH=. lean --run GokujoMain.lean scan RequestProject
./gokujo-fixed scan RequestProject
./gokujo-fixed check RequestProject
```
