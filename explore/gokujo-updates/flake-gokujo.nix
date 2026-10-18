{
  description = "gokujo — Lean 4 build tool (flake-parts + lean4-nix pattern)";

  inputs = {
    nixpkgs.follows = "lean4-nix/nixpkgs";
    flake-parts.url = "github:hercules-ci/flake-parts";
    lean4-nix.url = "github:lenianiva/lean4-nix";
  };

  outputs = inputs @ {
    nixpkgs,
    flake-parts,
    lean4-nix,
    ...
  }:
    flake-parts.lib.mkFlake {inherit inputs;} {
      systems = [
        "aarch64-darwin"
        "aarch64-linux"
        "x86_64-darwin"
        "x86_64-linux"
      ];

      perSystem = {
        system,
        pkgs,
        ...
      }: {
        _module.args.pkgs = import nixpkgs {
          inherit system;
          overlays = [(lean4-nix.readToolchainFile ./lean-toolchain)];
        };

        packages.default =
          (pkgs.lean.buildLeanPackage {
            name = "RequestProject";
            roots = ["RequestProject", "Gokujo"];
            src = pkgs.lib.cleanSource ./minimal;
          })
          .executable;

        devShells.default = pkgs.mkShell {
          packages = with pkgs.lean; [lean-all];
        };
      };
    };
}
