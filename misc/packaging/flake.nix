{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    relocatable.url = "github:elegios/relocatable.nix";
    relocatable.inputs.nixpkgs.follows = "nixpkgs";
    # NOTE: to build this bundle against local checkouts, override with
    #   --override-input miking "git+file://<repo>?dir=misc/packaging"
    # and NOT with `path:<repo>/misc/packaging`.  `miking-lib.nix` uses
    # `src = ../..`, which escapes the store path when the flake root is the
    # subdirectory itself, and evaluation fails with the quite unhelpful
    # `error: path '/nix' does not exist`.  The `git+file:` form keeps the
    # repository root as the flake root, so `../..` resolves inside it.
    miking.url = "github:miking-lang/miking?dir=misc/packaging";
    miking.inputs.nixpkgs.follows = "nixpkgs";
    miking-dppl.url = "github:miking-lang/miking-dppl?dir=misc/packaging";
    miking-dppl.inputs.nixpkgs.follows = "nixpkgs";
    miking-dppl.inputs.miking.follows = "miking";
  };

  outputs = { self, nixpkgs, flake-utils, relocatable, miking, miking-dppl }:
    let
      mkPkg = system:
        let
          pkgs = nixpkgs.legacyPackages.${system}.pkgs;
          mpkgs = miking.packages.${system};
          mdpkgs = miking-dppl.packages.${system};
          treeppl-unwrapped = pkgs.callPackage ./treeppl-unwrapped.nix {
            inherit (mpkgs) miking-lib miking-unwrapped;
            inherit (mdpkgs) miking-dppl-lib;
          };
          treeppl-tmp-tar-gz = relocatable.bundlers.${system}.fixedLocationTarGz {
            drv = treeppl-unwrapped;
            tarName = "${treeppl-unwrapped.name}-${system}";
            extraSetup = dep: ''
              for site in ${dep}/lib/ocaml/*/site-lib; do
                OCAMLPATH="$site''${OCAMLPATH:+:''${OCAMLPATH}}"
              done
              export OCAMLPATH
              for mcore in ${dep}/lib/mcore/*; do
                # NOTE: `''${mcore##*/}` rather than `$(basename "$mcore")`.
                # This loop runs before PATH has necessarily gained the
                # dependency that provides coreutils -- the entries are added
                # in topological order -- so calling `basename` here fails
                # with `basename: command not found` on a bare PATH and takes
                # the whole wrapper down with it (`set -o errexit`).  Bash
                # parameter expansion needs no external command.
                MCORE_LIBS="''${mcore##*/}=$mcore''${MCORE_LIBS:+:''${MCORE_LIBS}}"
              done
              export MCORE_LIBS
            '';
            # NOTE: owl used to be listed here; `mi-stats` supersedes it and
            # arrives via miking-lib's site-lib, which the OCAMLPATH loop
            # above collects.  pkgs.stdenv.cc stays: it is what links the
            # generated programs, and now also supplies libstdc++.
            # NOTE: `findutils` is required at *compile* time by the bundled
            # `tpplc`, which locates its auto-import standard library by
            # shelling out to
            #   find <treeppl lib>/auto-import -type f -a -name '*.tppl'
            # Without `find` on PATH that list comes back empty, every
            # auto-imported binding silently disappears, and compiling any
            # model dies with a misleading `Unknown variable in symbolize:
            # length`.  Nothing points at the missing tool, so this is worth
            # keeping listed explicitly.  (Unrelated to the owl removal --
            # `mi-stats` arrives via miking-lib's site-lib, which the
            # OCAMLPATH loop above collects, and it links correctly.)
            runtimeInputs = [
              pkgs.ocamlPackages.findlib
              pkgs.stdenv.cc
              pkgs.findutils
              mdpkgs.miking-dppl-lib
            ];
          };
        in
          rec {
            packages.treeppl-unwrapped = treeppl-unwrapped;
            packages.tpplc-tmp-tar-gz = treeppl-tmp-tar-gz;
            devShells.default = pkgs.mkShell {
              name = "TreePPL dev shell";
              inputsFrom = [ packages.treeppl-unwrapped ];
              buildInputs = [ pkgs.gdb pkgs.tup ];
            };
          };
    in flake-utils.lib.eachDefaultSystem mkPkg // rec {
      overlays.treeppl = final: prev: {
        treeppl-unwrapped = final.callPackage ./treeppl-unwrapped.nix {};
      };
      overlays.default = overlays.treeppl;
    };
}
