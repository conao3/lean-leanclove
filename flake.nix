{
  description = "leanclove: Clojure core functions with Lean proofs";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-parts.url = "github:hercules-ci/flake-parts";
    treefmt-nix.url = "github:numtide/treefmt-nix";
  };

  outputs =
    inputs:
    inputs.flake-parts.lib.mkFlake { inherit inputs; } {
      imports = [ inputs.treefmt-nix.flakeModule ];

      systems = [
        "x86_64-linux"
        "aarch64-darwin"
      ];

      perSystem =
        { pkgs, config, ... }:
        {
          packages.default = pkgs.stdenv.mkDerivation {
            pname = "leanclove";
            version = "0.1.0";
            src = pkgs.lib.fileset.toSource {
              root = ./.;
              fileset = pkgs.lib.fileset.unions [
                ./lakefile.toml
                ./lake-manifest.json
                ./lean-toolchain
                ./LeanClove.lean
                ./LeanClove
                ./LeanCloveTest.lean
                ./Makefile
                ./LICENSE
              ];
            };
            nativeBuildInputs = [ pkgs.lean4 ];
            buildPhase = ''
              runHook preBuild
              export HOME="$TMPDIR"
              make proof-check test
              runHook postBuild
            '';
            installPhase = ''
              runHook preInstall
              mkdir -p "$out"
              cp -r LeanClove.lean LeanClove lakefile.toml lake-manifest.json lean-toolchain LICENSE "$out/"
              cp -r .lake/build "$out/build"
              runHook postInstall
            '';
          };

          treefmt = {
            projectRootFile = "flake.nix";
            programs.nixfmt.enable = true;
          };

          devShells.default = pkgs.mkShell {
            packages = [
              pkgs.lean4
              config.treefmt.build.wrapper
            ];
          };
        };
    };
}
