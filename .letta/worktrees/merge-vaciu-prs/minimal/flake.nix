{
  description = "gokujo — single-file Lean 4 toolchain for RequestProject";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
  };

  outputs = { self, nixpkgs }:
    let
      pkgs = nixpkgs.legacyPackages.x86_64-linux;
      lean = pkgs.lean4;
      leanc = pkgs.leanc;
      lake = pkgs.lake;
    in {
      devShells.default = pkgs.mkShell {
        name = "gokujo-dev";
        buildInputs = [ lean leanc lake git ];
        shellHook = ''
          echo "gokujo dev shell ready"
          echo "Run: lean --make Gokujo.lean"
          echo "Run: ./gokujo check RequestProject"
        '';
      };

      packages.gokujo = pkgs.stdenv.mkDerivation {
        name = "gokujo";
        src = self;
        buildInputs = [ lean leanc ];
        buildPhase = ''
          cd minimal
          lean --make Gokujo.lean -o gokujo-stage1
        '';
        installPhase = ''
          mkdir -p $out/bin
          cp minimal/gokujo-stage1 $out/bin/gokujo
        '';
      };
    };
}
