{ packages ? "agdaPackages"
, rev      ? "502845c3e31ef3de0e424f3fcb09217df2ce6df6"
, sha256   ? "0fcqpsy6y7dgn0y0wgpa56gsg0b0p8avlpjrd79fp4mp9bl18nda"
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
  name = "cat-linear-${version}";
  version = "1.0";

  src = ./.;

  buildInputs = [
    (agda.withPackages (p:
       let standard-library =
             (p.standard-library.overrideAttrs (attrs: {
               version = "master";
               src = vendor/agda-stdlib;
              })); in
       [ standard-library
         ((p.agda-categories.override { inherit standard-library; })
                            .overrideAttrs (attrs: {
            # version = "0.1.3.1";
            version = "master";
            src = vendor/agda-categories;
          }))
       ]))
    pkgs.findutils
    pkgs.parallel
  ];

  buildPhase = ''
    set -e # fail if any file fails to typecheck

    # jww (2020-10-28): We cannot use --compile at the moment, because some
    # files (such as Biproduct.agda) take almost four hours to compile.

    find src -name Old -prune -o                      \
             -name '*.agda' -type f -print0           \
        | parallel --will-cite -0 -j $NIX_BUILD_CORES \
              "cd {//} && agda --no-main {/}"
  '';

  installPhase = ''
    mkdir -p $out
    cp -pR src $out
  '';

  env = pkgs.buildEnv { name = name; paths = buildInputs; };
}
