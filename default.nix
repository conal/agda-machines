{ packages ? "agdaPackages"
, rev      ? "c0e881852006b132236cbf0301bd1939bb50867e"
, sha256   ? "0fy7z7yxk5n7yslsvx5cyc6h21qwi4bhxf3awhirniszlbvaazy2"
, pkgs     ? import (builtins.fetchTarball {
    url = "https://github.com/jwiegley/nixpkgs/archive/${rev}.tar.gz";
    inherit sha256; }) {
    config.allowUnfree = true;
    config.allowBroken = false;
    overlays = [];
  }
}:

with pkgs.${packages};

pkgs.stdenv.mkDerivation rec {
  name = "machines-${version}";
  version = "1.0";

  src = ./.;

  buildInputs = [
    (agda.withPackages [ standard-library ])
    # (agda.withPackages (p:
    #    let standard-library =
    #          (p.standard-library.overrideAttrs (attrs: {
    #            version = "master";
    #            src = vendor/agda-stdlib;
    #           })); in
    #    [ standard-library
    #      ((p.agda-categories.override { inherit standard-library; })
    #                         .overrideAttrs (attrs: {
    #         # version = "0.1.3.1";
    #         version = "master";
    #         src = vendor/agda-categories;
    #       }))
    #    ]))
    pkgs.findutils
    pkgs.parallel
    pkgs.graphviz
  ];

  buildPhase = ''
    set -e # fail if any file fails to typecheck

    # jww (2020-10-28): We cannot use --compile at the moment, because some
    # files (such as Biproduct.agda) take almost four hours to compile.

    make
    # find src -name Old -prune -o                      \
    #          -name '*.agda' -type f -print0           \
    #     | parallel --will-cite -0 -j $NIX_BUILD_CORES \
    #           "cd {//} && agda --no-main {/}"
  '';

  installPhase = ''
    mkdir -p $out
    # cp -pR src $out
  '';

  env = pkgs.buildEnv { name = name; paths = buildInputs; };
}
