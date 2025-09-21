{
  description = "CSB (Count and Sample on Bitvectors)";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";
    arjun = {
      url = "github:meelgroup/arjun/58ec9aff687c9adcd6a26f158a947c07794e43f6";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    cryptominisat = {
      url = "github:msoos/cryptominisat/b09bd6bf05253adf5981e44f9dbd374b2811ff94";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    sbva = {
      url = "github:meelgroup/sbva/0faa08cf3cc26ed855831c9dc16a3489c9ae010f";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    approxmc = {
      url = "github:meelgroup/approxmc/56042dc9002dee312bb4be283d2bdf8bc2a67827";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    breakid = {
      url = "github:meelgroup/breakid/dee9744b7041cec373aa0489128b06a40fce43a1";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    cmsgen = {
      url = "github:arijitsh/cmsgen/bad5007705c99122f7417ee585aa58bd00cfe491";
      flake = false;
    };
    ganak = {
      url = "github:meelgroup/ganak/c060a9083e7f5477fa86b226030fc8cb32259ab1";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    minisat = {
      url = "github:stp/minisat/14c78206cd12d1d36b7e042fa758747c135670a4";
      flake = false;
    };
    unigen = {
      url = "github:meelgroup/unigen/c6823b3aa5cc37335f018eabcc9cc27790519d41";
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
      minisat,
      unigen,
    }:
    let
      inherit (nixpkgs) lib;
      systems = lib.intersectLists lib.systems.flakeExposed (lib.platforms.linux ++ lib.platforms.darwin);
      forAllSystems = lib.genAttrs systems;
      nixpkgsFor = forAllSystems (system: nixpkgs.legacyPackages.${system});

      unigenSrc = unigen;
      cmsgenSrc = cmsgen;
      minisatSrc = minisat;

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
          nativeBuildInputs =
            [
              cmake
              pkg-config
            ]
            ++ lib.optionals stdenv.hostPlatform.isLinux [ autoPatchelfHook ];
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

      cmsgen-package =
        {
          stdenv,
          cmake,
          pkg-config,
          autoPatchelfHook,
          zlib,
        }:
        stdenv.mkDerivation {
          pname = "cmsgen";
          version = "bad5007705c99122f7417ee585aa58bd00cfe491";
          src = cmsgenSrc;
          nativeBuildInputs =
            [
              cmake
              pkg-config
            ]
            ++ lib.optionals stdenv.hostPlatform.isLinux [ autoPatchelfHook ];
          buildInputs = [
            zlib
          ];
          cmakeFlags = [
            "-DSTATICCOMPILE=OFF"
          ];
          enableParallelBuilding = true;
        };

      minisat-package =
        {
          stdenv,
          cmake,
          pkg-config,
          zlib,
        }:
        stdenv.mkDerivation {
          pname = "minisat";
          version = "2.2.1";
          src = minisatSrc;
          nativeBuildInputs = [
            cmake
            pkg-config
          ];
          buildInputs = [
            zlib
          ];
          cmakeFlags = [
            "-DBUILD_SHARED_LIBS=ON"
            "-DSTATICCOMPILE=OFF"
          ];
          enableParallelBuilding = true;
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
          minisat,
          unigen,
          bison,
          flex,
          python3,
          python3Packages,
        }:
        stdenv.mkDerivation {
          name = "csb";
          nativeBuildInputs =
            [
              cmake
              pkg-config
              bison
              flex
              python3
              python3Packages.numpy
            ]
            ++ lib.optionals stdenv.hostPlatform.isLinux [ autoPatchelfHook ];
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
            minisat
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
          ganakPkg =
            (ganak.packages.${system}.ganak).overrideAttrs (old: {
              postInstall =
                (old.postInstall or "")
                + ''
                  mkdir -p "$out/lib/cmake/ganak"
                  cat > "$out/lib/cmake/ganak/ganakTargets.cmake" <<'EOF'
                  get_filename_component(_GANAK_PREFIX "''${GANAK_CMAKE_DIR}/../../.." ABSOLUTE)
                  set(_GANAK_LIBRARY "''${_GANAK_PREFIX}/lib/libganak''${CMAKE_SHARED_LIBRARY_SUFFIX}")
                  if(NOT EXISTS "''${_GANAK_LIBRARY}")
                    set(_GANAK_LIBRARY "''${_GANAK_PREFIX}/lib/libganak.so")
                  endif()
                  if(NOT TARGET ganak)
                    add_library(ganak SHARED IMPORTED)
                    set_target_properties(ganak PROPERTIES
                      IMPORTED_LOCATION "''${_GANAK_LIBRARY}"
                      INTERFACE_INCLUDE_DIRECTORIES "''${_GANAK_PREFIX}/include"
                      INTERFACE_LINK_LIBRARIES "gmp;mpfr;cryptominisat5;arjun;sbva;breakid;approxmc"
                    )
                  endif()
                  unset(_GANAK_PREFIX)
                  unset(_GANAK_LIBRARY)
                  EOF
                '';
            });
          cmsgenPkg = nixpkgsFor.${system}.callPackage cmsgen-package {};
          minisatPkg = nixpkgsFor.${system}.callPackage minisat-package {};
          csb = nixpkgsFor.${system}.callPackage csb-package {
            cryptominisat = cryptominisat.packages.${system}.cryptominisat;
            arjun = arjun.packages.${system}.arjun;
            sbva = sbva.packages.${system}.sbva;
            breakid = breakid.packages.${system}.breakid;
            approxmc = approxmc.packages.${system}.approxmc;
            flint3 = nixpkgsFor.${system}.flint;
            cmsgen = cmsgenPkg;
            ganak = ganakPkg;
            minisat = minisatPkg;
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

