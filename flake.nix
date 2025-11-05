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

      getSource = input: input.outPath or input;
      getRev = input:
        if input ? rev then input.rev
        else if input ? sourceInfo && input.sourceInfo ? rev then input.sourceInfo.rev
        else "unknown";
      nixpkgsRev = getRev nixpkgs;

      cadicalInput =
        if arjun ? inputs && arjun.inputs ? cadical then arjun.inputs.cadical
        else if cryptominisat ? inputs && cryptominisat.inputs ? cadical then cryptominisat.inputs.cadical
        else builtins.throw "cadical input unavailable";
      cadibackInput =
        if arjun ? inputs && arjun.inputs ? cadiback then arjun.inputs.cadiback
        else if cryptominisat ? inputs && cryptominisat.inputs ? cadiback then cryptominisat.inputs.cadiback
        else builtins.throw "cadiback input unavailable";

      arjunSrc = getSource arjun;
      approxmcSrc = getSource approxmc;
      breakidSrc = getSource breakid;
      cadicalSrc = getSource cadicalInput;
      cadibackSrc = getSource cadibackInput;
      cmsgenSrc = cmsgen;
      cryptominisatSrc = getSource cryptominisat;
      ganakSrc = getSource ganak;
      minisatSrc = minisat;
      sbvaSrc = getSource sbva;
      unigenSrc = unigen;

      cadicalVersion = getRev cadicalInput;
      cadibackVersion = getRev cadibackInput;
      cryptominisatVersion = getRev cryptominisat;
      arjunVersion = getRev arjun;
      approxmcVersion = getRev approxmc;
      sbvaVersion = getRev sbva;
      breakidVersion = getRev breakid;
      ganakVersion = getRev ganak;

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

      cadical-package =
        { stdenv }:
        stdenv.mkDerivation {
          pname = "cadical";
          version = cadicalVersion;
          src = cadicalSrc;
          configurePhase = ''
            ./configure --competition
          '';
          installPhase = ''
            mkdir -p $out/lib
            rm -f build/makefile
            cp -r configure src/ build/ $out
            cp build/libcadical.a $out/lib
            mkdir -p $out/include
            cp src/*.hpp $out/include
          '';
        };

      cadiback-package =
        {
          stdenv,
          git,
          cadical,
        }:
        stdenv.mkDerivation {
          pname = "cadiback";
          version = cadibackVersion;
          src = cadibackSrc;
          nativeBuildInputs = [ git ];
          buildInputs = [ cadical ];
          patchPhase = ''
            substituteInPlace makefile.in \
              --replace-fail "/usr/" "$out/" \
              --replace-fail "../cadical" "${cadical}"
            substituteInPlace generate \
              --replace-fail ${lib.escapeShellArg ''[ -d .git ] || die "could not find '.git' directory"''} "" \
              --replace-fail ${lib.escapeShellArg "`git show|head -1|awk '{print $2}'`"} ${lib.escapeShellArg nixpkgsRev}
          '';
          configurePhase = ''
            export CADICAL=${cadical}
            ./configure
          '';
          preInstall = ''
            mkdir -p $out/lib
            mkdir -p $out/include
          '';
          postInstall =
            lib.optionalString stdenv.hostPlatform.isDarwin ''
              if [ -f "$out/lib/libcadiback.dylib" ]; then
                install_name_tool -id "$out/lib/libcadiback.dylib" "$out/lib/libcadiback.dylib"
              elif [ -f "$out/lib/libcadiback.so" ]; then
                install_name_tool -id "$out/lib/libcadiback.so" "$out/lib/libcadiback.so"
              fi
            '';
        };

      sbva-package =
        {
          stdenv,
          cmake,
          autoPatchelfHook,
        }:
        stdenv.mkDerivation {
          pname = "sbva";
          version = sbvaVersion;
          src = sbvaSrc;
          nativeBuildInputs =
            [ cmake ]
            ++ lib.optionals stdenv.hostPlatform.isLinux [ autoPatchelfHook ];
        };

      breakid-package =
        {
          stdenv,
          cmake,
          autoPatchelfHook,
        }:
        stdenv.mkDerivation {
          pname = "breakid";
          version = breakidVersion;
          src = breakidSrc;
          nativeBuildInputs =
            [ cmake ]
            ++ lib.optionals stdenv.hostPlatform.isLinux [ autoPatchelfHook ];
        };

      ensmallen-package =
        {
          stdenv,
          cmake,
          fetchzip,
          armadillo,
        }:
        stdenv.mkDerivation {
          pname = "ensmallen";
          version = "2.22.2";
          src = fetchzip {
            url = "https://ensmallen.org/files/ensmallen-2.22.2.tar.gz";
            hash = "sha256-awM1Si6AcbAi4bfr2nrcGngcqTYMp9m6g3UPpMC4/Ok=";
          };
          nativeBuildInputs = [ cmake ];
          buildInputs = [ armadillo ];
        };

      mlpack-package =
        {
          stdenv,
          fetchFromGitHub,
          cmake,
          armadillo,
          ensmallen,
          cereal,
          pkg-config,
        }:
        stdenv.mkDerivation {
          pname = "mlpack";
          version = "4.6.2";
          src = fetchFromGitHub {
            owner = "mlpack";
            repo = "mlpack";
            rev = "4.6.2";
            hash = "sha256-HtxwUck9whHg/YLKJVJkNsh4zLIu6b0a+NeKICmB7uk=";
          };
          nativeBuildInputs = [
            pkg-config
            cmake
            armadillo
          ];
          buildInputs = [
            ensmallen
            cereal
          ];
        };

      cryptominisat-package =
        {
          stdenv,
          cmake,
          pkg-config,
          cadiback,
          cadical,
          gmp,
          zlib,
        }:
        stdenv.mkDerivation {
          pname = "cryptominisat";
          version = cryptominisatVersion;
          src = cryptominisatSrc;
          nativeBuildInputs = [
            cmake
            pkg-config
          ];
          buildInputs = [
            cadiback
            cadical
            gmp
            zlib
          ];
        };

      approxmc-package =
        {
          stdenv,
          cmake,
          autoPatchelfHook,
          gmp,
          mpfr,
          zlib,
          cryptominisat,
          arjun,
          sbva,
        }:
        stdenv.mkDerivation {
          pname = "approxmc";
          version = approxmcVersion;
          src = approxmcSrc;
          nativeBuildInputs =
            [ cmake ]
            ++ lib.optionals stdenv.hostPlatform.isLinux [ autoPatchelfHook ];
          buildInputs = [
            gmp
            mpfr
            zlib
            cryptominisat
            arjun
            sbva
          ];
        };

      arjun-package =
        {
          stdenv,
          cmake,
          sbva,
          zlib,
          gmp,
          mpfr,
          cadiback,
          mlpack,
          armadillo,
          cereal,
          ensmallen,
          cadical,
          cryptominisat5,
        }:
        stdenv.mkDerivation {
          pname = "arjun";
          version = arjunVersion;
          src = arjunSrc;
          nativeBuildInputs = [ cmake ];
          buildInputs = [
            zlib
            sbva
            gmp
            mpfr
            cadiback
            mlpack
            armadillo
            cereal
            ensmallen
            cadical
            cryptominisat5
          ];
        };

      ganak-package =
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
          python3,
          python3Packages,
        }:
        stdenv.mkDerivation {
          pname = "ganak";
          version = ganakVersion;
          src = ganakSrc;
          cmakeFlags = [
            "-DPython3_EXECUTABLE=${python3}/bin/python3"
          ];
          nativeBuildInputs =
            [
              cmake
              pkg-config
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
          ];
        };

      csb-package =
        {
          stdenv,
          cmake,
          pkg-config,
          boost,
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
          perl,
        }:
        stdenv.mkDerivation {
          name = "csb";
          cmakeFlags = [
            "-DPython3_EXECUTABLE=${python3}/bin/python3"
          ];
          nativeBuildInputs =
            [
              cmake
              pkg-config
              bison
              flex
              python3
              python3Packages.numpy
              perl
            ]
            ++ lib.optionals stdenv.hostPlatform.isLinux [ autoPatchelfHook ];
          buildInputs = [
            boost
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
          pkgs = nixpkgsFor.${system};
          cadicalPkg = pkgs.callPackage cadical-package { };
          cadibackPkg = pkgs.callPackage cadiback-package { cadical = cadicalPkg; };
          sbvaPkg = pkgs.callPackage sbva-package { };
          breakidPkg = pkgs.callPackage breakid-package { };
          ensmallenPkg = pkgs.callPackage ensmallen-package { };
          mlpackPkg = pkgs.callPackage mlpack-package { ensmallen = ensmallenPkg; };
          cryptominisatPkg = pkgs.callPackage cryptominisat-package {
            cadical = cadicalPkg;
            cadiback = cadibackPkg;
          };
          arjunPkg = pkgs.callPackage arjun-package {
            mlpack = mlpackPkg;
            ensmallen = ensmallenPkg;
            cadical = cadicalPkg;
            cadiback = cadibackPkg;
            cryptominisat5 = cryptominisatPkg;
            sbva = sbvaPkg;
          };
          approxmcPkg = pkgs.callPackage approxmc-package {
            cryptominisat = cryptominisatPkg;
            arjun = arjunPkg;
            sbva = sbvaPkg;
          };
          unigen = pkgs.callPackage unigen-package {
            cryptominisat = cryptominisatPkg;
            arjun = arjunPkg;
            sbva = sbvaPkg;
            approxmc = approxmcPkg;
          };
          ganakBase = pkgs.callPackage ganak-package {
            cryptominisat = cryptominisatPkg;
            arjun = arjunPkg;
            sbva = sbvaPkg;
            breakid = breakidPkg;
            approxmc = approxmcPkg;
          };
          ganakPkg =
            ganakBase.overrideAttrs (old: {
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
          cmsgenPkg = pkgs.callPackage cmsgen-package { };
          minisatPkg = pkgs.callPackage minisat-package { };
          csb = pkgs.callPackage csb-package {
            cryptominisat = cryptominisatPkg;
            arjun = arjunPkg;
            sbva = sbvaPkg;
            breakid = breakidPkg;
            approxmc = approxmcPkg;
            flint3 = pkgs.flint;
            cmsgen = cmsgenPkg;
            ganak = ganakPkg;
            minisat = minisatPkg;
            unigen = unigen;
          };
        in
        {
          inherit csb unigen;
          cmsgen = cmsgenPkg;
          mlpack = mlpackPkg;
          default = csb;
        }
      );
    };
}

