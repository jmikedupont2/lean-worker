/-! Builder — native `gokujo` GitHub Action cache-and-reuse strategy
-/

namespace Builder

/-- The native gokujo executable name. -/
def gokujoExe : String := "gokujo"

/-- Convert a Nat to its decimal String. -/
def natToString (n : Nat) : String :=
  String.ofList (Nat.toDigits 10 n)

/-- Compute a cheap deterministic fingerprint of a file path. -/
def fileFingerprint (p : String) : Nat :=
  let rec dig (n : Nat) (cs : List Char) : Nat :=
    if n == 0 then 0
    else
      match cs with
      | [] => 0
      | c :: cs => (dig (n - 1) cs + c.toNat) % 16384
  dig 128 p.toList

/-- Read a file, returning the empty string if it does not exist. -/
def readFileSafe (srcRoot : String) (p : String) : IO String := do
  (try IO.FS.readFile (srcRoot ++ "/" ++ p) catch _ => return "")

/-- Compute a cache key from the hashes of the builder source files.
This makes the GitHub Action cache invalidate automatically when the
builder source changes. -/
def cacheKey (srcRoot : String := "minimal") : IO String := do
  let files : List String :=
    ["Gokujo.lean", "GokujoMain.lean", "Builder.lean", ".github/workflows/lean.yml"]
  let digests ←
    List.mapM
      (fun p => readFileSafe srcRoot p >>= fun cs => return (fileFingerprint cs))
      files
  return "gh-action-gokujo-" ++ String.intercalate "-" (digests.map natToString)

/-- The bootstrap step text used in the GitHub Action workflow. -/
def bootstrapCmd : String := "gokujo bootstrap -o gokujo --backend bundled"

/-- A GitHub Actions check-step whose body is a multi-line shell script.
Defined as a plain String composed of "..." segments appended with
+, each \n inside a segment being a single newline in the output.
This avoids the s"-" raw-string escape problems entirely.
def builderGokujoBuildStep : String :=
  "- name: Build native gokujo (cache)" + "\n" +
  "    run: |" + "\n" +
  "      # Build the self-contained gokujo binary once per source change and cache it." + "\n" +
  "      if [ -f .gokujo/build/gokujo ]; then" + "\n" +
  "        echo 'GOKUJO=$(pwd)/.gokujo/build/gokujo' >> \"$GITHUB_ENV" + "\n" +
  "      else" + "\n" +
  "        echo 'GOKUJO=$(pwd)/.gokujo/build/gokujo' >> \"$GITHUB_ENV" + "\n" +
  "        mkdir -p .gokujo/build" + "\n" +
  "        { cat minimal/Gokujo.lean" + "\n" +
  "          echo 'def main (argv : List String) : IO UInt32 := gokujoMain argv'; } > minimal/gokujo-main.lean" + "\n" +
  "        (cd minimal && lean -c gokujo-main.c gokujo-main.lean)" + "\n" +
  "        leanc gokujo-main.c -o .gokujo/build/gokujo || exit $?" + "\n" +
  "      fi" + "\n" +
  "      # Surface the binary version in CI so a stale cache is caught." + "\n" +
  "      $GOKUJO version || true"

/-- A GitHub Actions check-step that reuses the cached native gokujo binary.
Fails the step (with a clear message) if the cache missed so CI visibly
does not silently fall back to rebuilding.
def builderGokujoUseStep : String :=
  "- name: Use cached native gokujo" + "\n" +
  "    run: |" + "\n" +
  "      if [ ! -x $GOKUJO ]; then" + "\n" +
  "        echo 'GOKUJO=' >> \"$GITHUB_ENV" + "\n" +
  "        echo 'gokujo cache miss - rebuild (see build-native-gokujo step) >&2'" + "\n" +
  "        exit 1" + "\n" +
  "      else" + "\n" +
  "        echo 'GOKUJO=$(realpath -s $GOKUJO)' >> \"$GITHUB_ENV" + "\n" +
  "      fi"

/-- The complete GitHub Actions workflow that builds gokujo once, caches the
binary, and reuses it for the git_twin solve step instead of rebuilding every
run. Uses matrix backends [bundled, system, elan, lake, nix].
def githubWorkflow : String :=
  "name: Lean 4 Builder + git_twin" + "\n" +
  "\n" +
  "on:" + "\n" +
  "  push:" + "\n" +
  "    branches: [ main ]" + "\n" +
  "  pull_request:" + "\n" +
  "    branches: [ main ]" + "\n" +
  "  schedule:" + "\n" +
  "    - cron: '0 3 * * *'  # daily at 03:00 UTC - keep the twin report fresh" + "\n" +
  "\n" +
  "jobs:" + "\n" +
  "  build-gokujo:" + "\n" +
  "    runs-on: ubuntu-latest" + "\n" +
  "    strategy:" + "\n" +
  "      matrix:" + "\n" +
  "        backend: [bundled, system, elan, lake, nix]" + "\n" +
  "    steps:" + "\n" +
  "      - uses: actions/checkout@v4" + "\n" +
  "        with:" + "\n" +
  "          fetch-depth: 0" + "\n" +
  "\n" +
  "      - name: Setup Nix (toolchain)" + "\n" +
  "        if: matrix.backend == 'nix'" + "\n" +
  "        uses: cachix/install-nix-action@v20" + "\n" +
  "        with:" + "\n" +
  "          extra_nix_config: |" + "\n" +
  "            experimental-features = nix-command flakes" + "\n" +
  "            substituters = https://cache.nixos.org https://nix-community.cachix.org" + "\n" +
  "            trusted-public-keys = cache.nixos.org-1:aNJVHp2ql7migYbNxr0vczfzuVoCYuzzbJVGNCDtU6g= nix-community.cachix.org-1:IT9/7Hwk9xU/HRhDHbhlZW6Nw3NUBmEvfpL6wO3jVNo=" + "\n" +
  "\n" +
  "      - name: Install Lean 4 toolchain" + "\n" +
  "        if: matrix.backend != 'nix'" + "\n" +
  "        run: |" + "\n" +
  "          nix profile install nixpkgs#lean4" + "\n" +
  "          nix profile install nixpkgs#leanc" + "\n" +
  "\n" +
  "      - name: Cache native gokujo build" + "\n" +
  "        id: gokujo-cache" + "\n" +
  "        uses: actions/cache@v4" + "\n" +
  "        with:" + "\n" +
  "          path: minimal/.gokujo" + "\n" +
  "          key: \"" + "${{ runner.os }}-gokujo-" + "${{ matrix.backend }}-" + "${{ hashFiles('minimal/Gokujo.lean', 'minimal/GokujoMain.lean', 'minimal/Builder.lean') }}-builder" + "\n" +
  "          restore-keys: |" + "\n" +
  "            \"${{ runner.os }}-gokujo-" + "${{ matrix.backend }}-" + "\n" +
  "            \"${{ runner.os }}-gokujo-" + "\n" +
  "            \"${{ runner.os }}-gokujo-" + "\n" +
  "\n" +
  "      - name: Build native gokujo" + "\n" +
  "        run: |" + "\n" +
  "          make -C minimal builder" + "\n" +
  "        env:" + "\n" +
  "          GOKUJO_BACKEND: \"" + "${{ matrix.backend }}" + "\n" +
  "\n" +
  "      - name: Run git_twin (solve)" + "\n" +
  "        run: |" + "\n" +
  "          node .github/workflows/solve_git_twin.mjs" + "\n" +
  "        env:" + "\n" +
  "          GH_TOKEN: \"" + "${{ secrets.GITHUB_TOKEN }}" + "\n" +
  "          GH_REPO: jmikedupont2/lean-worker" + "\n" +
  "          BRANCH: main" + "\n" +
  "          RELAY: https://kant-zk-relay.jmikedupont2.workers.dev" + "\n" +
  "          RELAY_ROOM: agent-zoo-public" + "\n" +
  "          SALT: twin-proof-wave-vi-xii-2026-09-17-mike" + "\n" +
  "          NODE_ID: github-actions-${{ github.run_id }}" + "\n" +
  "\n" +
  "      - name: Publish twin status" + "\n" +
  "        if: always()" + "\n" +
  "        run: |" + "\n" +
  "          node -e \"import('./.github/workflows/solve_git_twin.mjs').then(async m => { await m.postToRelay({ kind: 'solve_git_twin_status', status: 'published', run: ${{ github.run_id }}, node: process.env.NODE_ID, ts: Date.now() })});\"" + "\n"

end Builder
