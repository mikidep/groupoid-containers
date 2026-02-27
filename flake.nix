{
  description = "Agda library on containers";
  inputs = {
    nixpkgs.url = "nixpkgs/nixos-unstable";
    agda-index = {
      url = "github:phijor/agda-index?ref=418fb0";
      # inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  # Flake outputs
  outputs = inputs @ {nixpkgs, ...}: let
    # The systems supported for this flake
    supportedSystems = [
      "x86_64-linux" # 64-bit Intel/AMD Linux
      "aarch64-linux" # 64-bit ARM Linux
      "x86_64-darwin" # 64-bit Intel macOS
      "aarch64-darwin" # 64-bit ARM macOS
    ];

    # Helper to provide system-specific attributes
    forEachSupportedSystem = f:
      nixpkgs.lib.genAttrs supportedSystems (system:
        f {
          inherit system;
          pkgs = import nixpkgs {
            inherit system;
          };
        });
  in {
    packages = forEachSupportedSystem ({
      pkgs,
      system,
    }: let
      cubical = pkgs.agdaPackages.cubical;
      deps = [cubical];

      cubicalEverything =
        pkgs.runCommand "cubical-everything" {
          inherit (cubical) src version;
        } ''
          mkdir $out
          cd $src
          sh generate-everything.sh > $out/Everything.agda
          sed -i 's/module Cubical\./module /' $out/Everything.agda
        '';
      cubicalDocs =
        pkgs.runCommand "cubical-docs" {
          inherit (cubical) version;
          src = cubicalEverything;
          buildInputs = [(pkgs.agda.withPackages [cubical])];
        } ''
          mkdir $out
          cp $src/Everything.agda .
          agda -i . Everything.agda -l cubical \
            --safe --guardedness --cubical \
            --html --html-dir $out
        '';
    in rec {
      devshell = pkgs.symlinkJoin [(pkgs.agda.withPackages deps) agda-search];
      groupoid-containers = pkgs.agdaPackages.mkDerivation {
        pname = "groupoid-containers";
        version = "0.1";
        src = ./.;
        buildInputs = [cubical];
        meta = {
          platforms = pkgs.lib.platforms.all;
        };
      };
      # docs are broken
      # docs = agdaDocsGen groupoid-containers "Everything.agda";
      cubical-docs = cubicalDocs;
      default = groupoid-containers;
      agda-search = pkgs.writeShellApplication {
        name = "agda-search";
        runtimeInputs = with pkgs; [fzf firefox (inputs.agda-index.packages.${system}.default)];
        text = ''
          agda-index ${cubical-docs}/*.html | fzf -d' ' --with-nth='2' | cut -d' ' -f1 | xargs -I % firefox --new-window %
        '';
      };
    });
  };
}
