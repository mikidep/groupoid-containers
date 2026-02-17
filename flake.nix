{
  description = "Agda library on containers";
  inputs = {
    nixpkgs.url = "nixpkgs/nixos-unstable";
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

      agdaDocsGen = agdalib: rootModule:
        pkgs.agdaPackages.mkDerivation {
          pname = agdalib.pname + "-docs";
          inherit (agdalib) version src;
          buildInputs = [agdalib] ++ agdalib.buildInputs;
          buildPhase = ''
            runHook preBuild
            mkdir docshim
            mv *.agda-lib docshim/
            mkdir -p docshim/$(dirname ${rootModule})
            mv ${rootModule} docshim/${rootModule}
            cd docshim
            cat ${rootModule}
            sed -i 's/^name:.*$/name: docshim/g' *.agda-lib
            sed -i 's/^depend:.*$/depend: ${agdalib.pname}/g' *.agda-lib
            sed -i 's/^src:.*$/src: ./g' *.agda-lib
            mkdir $out
            agda --html --html-dir=$out ${rootModule}
            runHook postBuild
          '';
          meta = {};
        };
    in rec {
      devshell = pkgs.agda.withPackages deps;
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
      # cubical-docs = (agdaDocsGen cubical "Cubical/Everything.agda").overrideAttrs (_: prev: {
      #   buildPhase =
      #     ''
      #       sh generate-everything.sh > Everything.agda
      #       mv Everything.agda Cubical/
      #     ''
      #     + prev.buildPhase;
      # });
      default = groupoid-containers;
      # agda-search = pkgs.writeShellApplication {
      #   name = "agda-search";
      #   runtimeInputs = with pkgs; [fzf firefox (agda-index.packages.${system}.default)];
      #   text = ''
      #     agda-index ${docs}/ | fzf -d' ' --with-nth='2' | cut -d' ' -f1 | xargs -I % firefox --new-window %
      #   '';
      # };
    });
  };
}
