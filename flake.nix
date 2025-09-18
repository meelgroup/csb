{
  description = "CSB (Count and Sample on Bitvectors)";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";
    arjun = {
      url = "github:meelgroup/arjun/master";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    cryptominisat = {
      url = "github:msoos/cryptominisat/master";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    sbva = {
      url = "github:meelgroup/sbva/master";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    approxmc = {
      url = "github:meelgroup/approxmc/master";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    breakid = {
      url = "github:meelgroup/breakid/master";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    cmsgen = {
      url = "github:meelgroup/cmsgen/master";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    ganak = {
      url = "github:meelgroup/ganak/master";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    unigen = {
      url = "github:meelgroup/unigen/master";
      flake = false;
    };
  };

  outputs =
    {
      self,
      nixpkgs,
      arjun,
      approxmc,
      breakid,
      cryptominisat,
      sbva,
      cmsgen,
      ganak,
      unigen,
    }:
    let
      inherit (nixpkgs) lib;
      systems = lib.intersectLists lib.systems.flakeExposed (lib.platforms.linux ++ lib.platforms.darwin);
      forAllSystems = lib.genAttrs systems;
      nixpkgsFor = forAllSystems (system: nixpkgs.legacyPackages.${system});

      unigenSrc = unigen;

      unigen-package =
        {
          stdenv,
          cmake,
          pkg-config,
          autoPatchelfHook,
          gmp,
          mpfr,
          zlib,
          cryptominisat,
          arjun,
          sbva,
          approxmc,
        }:
        stdenv.mkDerivation {
          name = "unigen";
          src = unigenSrc;
          nativeBuildInputs = [
            cmake
            pkg-config
            autoPatchelfHook
          ];
          buildInputs = [
            gmp
            mpfr
            zlib
            cryptominisat
            arjun
            sbva
            approxmc
          ];
        };

      csb-package =
        {
          stdenv,
          cmake,
          pkg-config,
          gmp,
          mpfr,
          flint3,
          zlib,
          autoPatchelfHook,
          cryptominisat,
          arjun,
          sbva,
          breakid,
          approxmc,
          cmsgen,
          ganak,
          unigen,
          python3,
          python3Packages,
        }:
        stdenv.mkDerivation {
          name = "csb";
          nativeBuildInputs = [
            cmake
            pkg-config
            autoPatchelfHook
            python3
            python3Packages.numpy
          ];
          buildInputs = [
            gmp
            mpfr
            flint3
            zlib
            cryptominisat
            arjun
            sbva
            breakid
            approxmc
            cmsgen
            ganak
            unigen
          ];
          src = ./.;
        };
    in
    {
      devShells = forAllSystems (
        system:
        let
          pkgs = nixpkgsFor.${system};
        in
        {
          default = pkgs.mkShell {
            packages = [
              pkgs.cmake
              pkgs.pkg-config
              pkgs.gmp
            ];
          };
        }
      );

      packages = forAllSystems (
        system:
        let
          unigen = nixpkgsFor.${system}.callPackage unigen-package {
            cryptominisat = cryptominisat.packages.${system}.cryptominisat;
            arjun = arjun.packages.${system}.arjun;
            sbva = sbva.packages.${system}.sbva;
            approxmc = approxmc.packages.${system}.approxmc;
          };
          ganakPkg = ganak.packages.${system}.ganak;
          cmsgenPkg = cmsgen.packages.${system}.cmsgen;
          csb = nixpkgsFor.${system}.callPackage csb-package {
            cryptominisat = cryptominisat.packages.${system}.cryptominisat;
            arjun = arjun.packages.${system}.arjun;
            sbva = sbva.packages.${system}.sbva;
            breakid = breakid.packages.${system}.breakid;
            approxmc = approxmc.packages.${system}.approxmc;
            flint3 = nixpkgsFor.${system}.flint;
            cmsgen = cmsgenPkg;
            ganak = ganakPkg;
            unigen = unigen;
          };
        in
        {
          inherit csb unigen;
          cmsgen = cmsgenPkg;
          default = csb;
        }
      );
    };
}

