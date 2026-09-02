{
  description = "Agda library on containers";
  inputs = {
    nixpkgs.url = "nixpkgs/nixos-unstable";
    flake-parts.url = "github:hercules-ci/flake-parts";
    agda = {
      url = "github:agda/agda?ref=55fbe4f";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    agda-index = {
      url = "github:phijor/agda-index?ref=418fb0";
    };
  };

  # Flake outputs
  outputs = inputs @ {flake-parts, ...}:
    flake-parts.lib.mkFlake {inherit inputs;} (top: {
      systems = [
        "x86_64-linux" # 64-bit Intel/AMD Linux
        "aarch64-linux" # 64-bit ARM Linux
        "x86_64-darwin" # 64-bit Intel macOS
        "aarch64-darwin" # 64-bit ARM macOS
      ];
      perSystem = {
        system,
        inputs',
        ...
      }: let
        pkgs = import inputs.nixpkgs {
          inherit system;
          overlays = [
            inputs.agda.overlays.default
          ];
        };
        agdaWithPackages = ps:
          pkgs.agda.withPackages {
            pkgs = ps;
            ghc = null;
          };
        cubical = pkgs.agdaPackages.cubical;
      in rec {
        _module.args = {inherit pkgs;};
        packages = {
          groupoid-containers = pkgs.agdaPackages.mkDerivation {
            pname = "groupoid-containers";
            version = "0.1";
            src = ./.;
            buildInputs = [cubical];
            meta = {
              platforms = pkgs.lib.platforms.all;
            };
          };
          cubical-docs = let
            cubicalEverything =
              pkgs.runCommand "cubical-everything" {
                inherit (cubical) src version;
              } ''
                mkdir $out
                cd $src
                sh generate-everything.sh > $out/Everything.agda
                sed -i 's/module Cubical\./module /' $out/Everything.agda
              '';
          in
            pkgs.runCommand "cubical-docs" {
              inherit (cubical) version;
              src = cubicalEverything;
              buildInputs = [(agdaWithPackages [cubical])];
            } ''
              mkdir $out
              cp $src/Everything.agda .
              agda -i . Everything.agda -l cubical \
                --safe --guardedness --cubical \
                --html --html-dir $out
            '';
          default = packages.groupoid-containers;
          agda-search = pkgs.writeShellApplication {
            name = "agda-search";
            runtimeInputs = with pkgs; [fzf (inputs'.agda-index.packages.default)];
            text = ''
              agda-index ${packages.cubical-docs}/*.html \
                | fzf -d' ' --with-nth='2' \
                | cut -d' ' -f1 \
                | xargs -I % firefox --new-window %
            '';
          };
        };
        devShells.default = pkgs.mkShell {
          packages = [(agdaWithPackages [cubical]) packages.agda-search];
        };
      };
    });
}
