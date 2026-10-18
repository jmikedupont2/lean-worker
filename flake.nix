{
  description = "lean-worker — formal twin of an AI agent on Aleph Cloud (Lean 4)";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    lean4.url = "github:leanprover/lean4";
    mathlib4.url = "github:leanprover-community/mathlib4";
    pipelight.url = "github:pipelight/pipelight";
    # gokujo is built locally from fixed source (iterative scanStr/walkLean) —
    # no github:mfng/gokujo input.
  };

  outputs = { self, nixpkgs, flake-utils, lean4, mathlib4, pipelight }:
    flake-utils.lib.eachDefaultSystem (system: let
      pkgs = nixpkgs.legacyPackages.${system};
      lean = pkgs.lean4;
      leanc = pkgs.leanc;
      lake = pkgs.lake;
      nix = pkgs.nix;
      # Local gokujo package: build the FIXED binary from source (iterative
      # scanStr/walkLean), replacing the github:mfng/gokujo placeholder that
      # 404s. Was previously `gokujo = self.packages.${system}.gokujo` via
      # flake-utils, which resolved to the broken placeholder input.
      localGokujo = pkgs.stdenv.mkDerivation {
        name = "gokujo";
        src = ./.;
        buildInputs = [ pkgs.lean pkgs.leanc ];
        buildPhase = ''cd minimal && lean --make Gokujo.lean -o gokujo-stage1'';
        installPhase = ''mkdir -p $out/bin && cp minimal/gokujo-stage1 $out/bin/gokujo'';
      };
      rp = self.packages.${system}.RequestProject;
      rp_share = "${rp}/share/lean";
    in {
      devShells.default = pkgs.mkShell {
        name = "lean-worker";
        buildInputs = [ pkgs.lean pkgs.leanc pkgs.lake pkgs.git pkgs.jq pkgs.curl pkgs.nix ];
        LEAN_PATH = rp_share + "";
        shellHook = ''
          echo "lean-worker dev shell ready"
          echo "Run: lake build    # standard Lake build"
          echo "Run: gokujo check  # gokujo single-file build + proof gate"
          echo "Run: gokujo bootstrap -o gokujo  # compile gokujo itself"
          echo "Run: gokujo html -o gokujo.html  # self-contained manual"
        '';
      };

      packages.RequestProject = pkgs.stdenv.mkDerivation {
        name = "lean-worker-RequestProject";
        src = self;
        buildInputs = [ pkgs.lean pkgs.leanc pkgs.lake ];
        buildPhase = ''
          cd minimal
          lake -d build RequestProject
        '';
        installPhase = ''
          mkdir -p $out/share/lean
          cp -r minimal/.lake/build/lib/RequestProject $out/share/lean/
        '';
      };

      # gokujo built locally from the fixed source (no github:mfng/gokujo).
      packages.gokujo = localGokujo;

      # Two-stage build: fast no-mathlib check, then full mathlib build
      checks = {
        "stage1-no-mathlib" = self.packages.${system}.gokujo;
        "stage2-full" = self.packages.${system}.RequestProject;
      };

      # pipelight.dev integration
      devPackages = {
        "pipelight-verify" = pipelight.packages.${system}.verify;
      };
    });
}
