{
  description = "A very basic flake";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs?ref=nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs =
    { nixpkgs, flake-utils, ... }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let 
        pkgs = nixpkgs.legacyPackages.${system};
        haranoaji-fonts = pkgs.stdenvNoCC.mkDerivation {
          name = "haranoaji";
          src = builtins.fetchGit {
            url = "https://github.com/trueroad/HaranoAjiFonts";
            ref = "master";
            rev = "00a817312cd4374f8e5821ae1a64b4aa04930ec4";
          };
          installPhase = ''
            mkdir -p $out
            cp -R $src $out
          '';
        };

      in {
        devShells.default = pkgs.mkShell {
          packages = [pkgs.typst];
          env = {
            TYPST_FONT_PATHS = "${haranoaji-fonts}";
          };
        };
      }
    );
}
