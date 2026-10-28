{
  inputs = {
    nixpkgs.follows = "lean4-nix/nixpkgs";
    flake-parts.url = "github:hercules-ci/flake-parts";
    lean4-nix.url = "github:lenianiva/lean4-nix";
  };
  outputs = inputs @ { nixpkgs, flake-parts, lean4-nix, ... }:
    flake-parts.lib.mkFlake {inherit inputs;} {
      systems = [ "x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin" ];
      perSystem = { system, pkgs, ... }: {
        _module.args.pkgs = import nixpkgs {
          inherit system;
          overlays = [ (lean4-nix.readToolchainFile ../minimal/lean-toolchain) ];
        };
        devShells.default = pkgs.mkShell {
          packages = with pkgs.lean; [ lean-all ] ++ [ pkgs.jq pkgs.gmp pkgs.libffi pkgs.pcre2 ];
        };
      };
    };
}
