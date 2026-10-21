/-! Builder — native `gokujo` GitHub Action cache-and-reuse strategy
-/

namespace Builder

/-- The executable this builder produces: the self-contained gokujo binary. -/
def gokujoExe : String := "gokujo"

/-- The cache key for the native gokujo build (hashes the source that must
compile, so a branch change invalidates the cache). -/
def cacheKey (srcRoot : String := "minimal") : String :=
  "gh-action-gokujo-" ++ Util.digest (Util.lines
    [ "Gokujo.lean", "GokujoMain.lean", "Builder.lean", ".github/workflows/lean.yml" ]
    .map (fun p => System.Process.getContents (srcRoot ++ "/" ++ p))
    .join)

/-- The bootstrap command that compiles native gokujo (no lake, no mathlib). -/
def bootstrapCmd : String := "gokujo bootstrap -o gokujo --backend bundled"

/-- The lean.yml step that builds native gokujo and caches it for the builder. -/
def builderGokujoBuildStep : String :=
  s!"- name: Build native gokujo (cache)
    run: |
      # Build the self-contained gokujo binary once per source change and cache it.
      if [ -f .gokujo/build/gokujo ]; then
        echo 'GOKUJO=$(pwd)/.gokujo/build/gokujo' >> \"$GITHUB_ENV\"
      else
        echo 'GOKUJO=$(pwd)/.gokujo/build/gokujo' >> \"$GITHUB_ENV\"
        mkdir -p .gokujo/build
        { cat minimal/Gokujo.lean
          echo 'def main (argv : List String) : IO UInt32 := gokujoMain argv'; } > minimal/gokujo-main.lean
        (cd minimal && lean -c gokujo-main.c gokujo-main.lean)
        leanc gokujo-main.c -o .gokujo/build/gokujo || exit $?
      fi
      # Surface the binary version in CI so a stale cache is caught.
      \"$GOKUJO\" version || true
  "

/-- The lean.yml step that reuses the cached native gokujo for verification. -/
def builderGokujoUseStep : String :=
  s!"- name: Use cached native gokujo
    run: |
      if [ ! -x \"$GOKUJO\" ]; then
        echo 'GOKUJO=' >> \"$GITHUB_ENV\"
        echo 'gokujo cache miss — rebuild (see build-native-gokujo step)' >&2
      else
        echo 'GOKUJO=$(realpath -s \"$GOKUJO\")' >> \"$GITHUB_ENV\"
      fi
  "

/-- The GitHub Actions workflow content generated for the builder (the native
gokujo action that caches the binary and runs `solve_git_twin`). -/
def githubWorkflow : String :=
  s!"name: Lean 4 Builder + git_twin

on:
  push:
    branches: [ main ]
  pull_request:
    branches: [ main ]
  schedule:
    - cron: '0 3 * * *'  # daily at 03:00 UTC — keep the twin report fresh

jobs:
  build-gokujo:
    runs-on: ubuntu-latest
    strategy:
      matrix:
        backend: [bundled, system, elan, lake, nix]
    steps:
      - uses: actions/checkout@v4
        with:
          fetch-depth: 0

      - name: Setup Nix (toolchain)
        if: matrix.backend == 'nix'
        uses: cachix/install-nix-action@v20
        with:
          extra_nix_config: |
            experimental-features = nix-command flakes
            substituters = https://cache.nixos.org https://nix-community.cachix.org
            trusted-public-keys = cache.nixos.org-1:aNJVHp2ql7migYbNxr0vczfzuVoCYuzzbJVGNCDtU6g= nix-community.cachix.org-1:IT9/7Hwk9xU/HRhDHbhlZW6Nw3NUBmEvfpL6wO3jVNo=

      - name: Install Lean 4 toolchain
        if: matrix.backend != 'nix'
        run: |
          nix profile install nixpkgs#lean4
          nix profile install nixpkgs#leanc

      - name: Cache native gokujo build
        id: gokujo-cache
        uses: actions/cache@v4
        with:
          path: minimal/.gokujo
          key: ${{ runner.os }}-gokujo-${{ matrix.backend }}-${{ hashFiles('minimal/Gokujo.lean', 'minimal/GokujoMain.lean', 'minimal/Builder.lean') }}
          restore-keys: |
            ${{ runner.os }}-gokujo-${{ matrix.backend }}-
            ${{ runner.os }}-gokujo-

      - name: Build native gokujo
        run: |
          make -C minimal builder
        env:
          GOKUJO_BACKEND: ${{ matrix.backend }}

      - name: Run git_twin (solve)
        run: |
          node .github/workflows/solve_git_twin.mjs
        env:
          GH_TOKEN: ${{ secrets.GITHUB_TOKEN }}
          GH_REPO: jmikedupont2/lean-worker
          BRANCH: main
          RELAY: https://kant-zk-relay.jmikedupont2.workers.dev
          RELAY_ROOM: agent-zoo-public
          SALT: twin-proof-wave-vi-xii-2026-09-17-mike
          NODE_ID: github-actions-${{ github.run_id }}

      - name: Publish twin status
        if: always()
        run: |
          node -e "import('./.github/workflows/solve_git_twin.mjs').then(async m => { await m.postToRelay({ kind: 'solve_git_twin_status', status: 'published', run: ${{ github.run_id }}, node: process.env.NODE_ID, ts: Date.now() }) });"
"

end Builder
