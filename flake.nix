{
  description = "lean-worker — formal twin of an AI agent on Aleph Cloud (Lean 4)";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    # `lean4` and `mathlib4` inputs were removed 2026-10-18. Nothing in
    # `outputs` ever referenced them (the toolchain is pkgs.lean from
    # nixpkgs), and the unlocked mathlib4 input made the WHOLE flake
    # un-evaluable on the tracker host with:
    #
    #   error: path '«github:leanprover-community/mathlib4/bbeef912…»/flake.nix' does not exist
    #
    # That failure reproduces standalone (nix 2.33.1):
    #   nix flake metadata github:leanprover-community/mathlib4
    # — a corrupt nix fetcher-cache entry for that input on that host, not a
    # defect in this flake's expressions. Deleting the dead inputs removed
    # the only consumer of the broken fetch. Mathlib is not part of any
    # check anyway: both stages are no-mathlib by policy (see
    # minimal/fast-lakefile.toml: "NO [[require]] = no mathlib, no network").
    pipelight.url = "github:pipelight/pipelight";
    # Session/usage tooling from llm-agents.nix (agentsview, ccusage,
    # cpa-usage-keeper, entire, mindwalk, tokscale). nixpkgs is deliberately
    # NOT followed: llm-agents.nix pins its own nixpkgs-unstable and publishes
    # daily builds to https://cache.numtide.com — following ours would rebuild
    # the Go/npm tooling from source and miss that cache (same note as
    # ~/projects/system-manager/flake.nix).
    llm-agents-src.url = "github:numtide/llm-agents.nix";
    # gokujo is built locally from fixed source (iterative scanStr/walkLean) —
    # no github:mfng/gokujo input (that placeholder 404s).
  };

  outputs = { self, nixpkgs, flake-utils, pipelight, llm-agents-src }:
    flake-utils.lib.eachDefaultSystem (system: let
      pkgs = nixpkgs.legacyPackages.${system};
      # agent session analytics / token-usage CLIs (see input note above)
      llmAgents = llm-agents-src.packages.${system};
      # Inside nix the toolchain is whatever nixpkgs carries (4.34.1 at the
      # nixpkgs-unstable revision locked in flake.lock); elan users get the
      # minimal/lean-toolchain pin (v4.28.0). Both compile the checked trees.
      #
      # One package, not three: nixpkgs has NO `leanc` or `lake` attributes
      # (checked 2026-10-18 — `pkgs.leanc` fails evaluation with "attribute
      # 'leanc' missing", `pkgs.lake` likewise). The lean4 package ships the
      # whole toolchain in one bin/: lean, leanc, lake, leanchecker, …

      # Local gokujo package: build the FIXED binary from source (iterative
      # scanStr/walkLean), replacing the github:mfng/gokujo placeholder that
      # 404s.
      #
      # Build-command defects fixed 2026-10-18:
      #   * `lean --make` no longer exists in the Lean 4 CLI — the pinned
      #     v4.28.0 toolchain rejects it with "unrecognized option '--make'";
      #   * `-o` writes an .olean, not an executable (that is lake's olean
      #     output flag), so the old `lean --make Gokujo.lean -o gokujo-stage1`
      #     could never have produced $out/bin/gokujo;
      #   * compiling Gokujo.lean alone cannot link a binary: its `def main`
      #     lives in `namespace Gokujo.Cli`, and Lean only emits the C `main`
      #     wrapper for a top-level `def main`. The entry point is the
      #     GokujoMain.lean shim (`def main := gokujoMain argv`), which used
      #     to import RequestProject.Tracker.Gokujo — a module that exists
      #     only in the tracker-side tree — so it failed to compile HERE.
      # The recipe below is what lake does, spelled out: olean + C per
      # module, then leanc to link both against libleanshared.
      localGokujo = pkgs.stdenv.mkDerivation {
        name = "gokujo";
        src = ./minimal;
        buildInputs = [ pkgs.lean4 ];
        buildPhase = ''
          runHook preBuild
          lean -o Gokujo.olean -c Gokujo.c Gokujo.lean
          LEAN_PATH="$PWD" lean -o GokujoMain.olean -c GokujoMain.c GokujoMain.lean
          leanc -O2 -o gokujo-stage1 Gokujo.c GokujoMain.c
          # prove the artifact actually runs, not just links
          ./gokujo-stage1 help > /dev/null
          runHook postBuild
        '';
        installPhase = ''
          runHook preInstall
          mkdir -p $out/bin
          cp gokujo-stage1 $out/bin/gokujo
          runHook postInstall
        '';
      };

      rp = self.packages.${system}.RequestProject;
      rp_share = "${rp}/share/lean";
    in {
      devShells.default = pkgs.mkShell {
        name = "lean-worker";
        buildInputs = [
          pkgs.lean4 pkgs.git pkgs.jq pkgs.curl pkgs.nix
          # agent session viewers + usage analytics (llm-agents.nix)
          llmAgents.agentsview llmAgents.ccusage llmAgents.cpa-usage-keeper
          llmAgents.entire llmAgents.mindwalk llmAgents.tokscale
        ];
        LEAN_PATH = rp_share;
        shellHook = ''
          echo "lean-worker dev shell ready"
          echo "Run: lake build    # standard Lake build"
          echo "Run: gokujo check  # gokujo single-file build + proof gate"
          echo "Run: gokujo bootstrap -o gokujo  # compile gokujo itself"
          echo "Run: gokujo html -o gokujo.html  # self-contained manual"
        '';
      };

      # pipelight integration. The old `devPackages."pipelight-verify" =
      # pipelight.packages.${system}.verify` referenced an attribute that
      # does not exist (pipelight exposes only `default`) — and devPackages
      # is not a flake output namespace at all, so `nix flake check` could
      # never evaluate it. Exposed as a real devShell instead.
      devShells.pipelight = pkgs.mkShell {
        name = "lean-worker-pipelight";
        buildInputs = [ pipelight.packages.${system}.default ];
      };

      # stage 2: the no-mathlib, no-network RequestProject tree, built via
      # minimal/fast-lakefile.toml (the default minimal/lakefile.toml does
      # not build: its root `Twin` imports GCP.*, which is not a declared
      # library). The old `lake -d build RequestProject` was also wrong —
      # lake's `-d` is `--dir` (it sets the package directory), so that line
      # ran a command literally named "RequestProject" out of a directory
      # named "build". -f selects the lakefile instead.
      packages.RequestProject = pkgs.stdenv.mkDerivation {
        name = "lean-worker-RequestProject";
        src = ./minimal;
        buildInputs = [ pkgs.lean4 ];
        buildPhase = ''
          runHook preBuild
          # lake must not write to $HOME (/homeless-shore in the sandbox)
          export HOME="$TMPDIR"
          lake -f fast-lakefile.toml build RequestProject
          runHook postBuild
        '';
        installPhase = ''
          runHook postInstall
          mkdir -p $out/share/lean
          cp -r .lake/build/lib/lean/RequestProject $out/share/lean/
          runHook postInstall
        '';
      };

      # gokujo built locally from the fixed source (no github:mfng/gokujo).
      packages.gokujo = localGokujo;

      # Two-stage build: fast no-mathlib check, then the RequestProject tree.
      checks = {
        "stage1-no-mathlib" = self.packages.${system}.gokujo;
        "stage2-full" = self.packages.${system}.RequestProject;
      };
    });
}
