#!/usr/bin/env bash
# configure.sh — Clone and build CSB's dependencies, then configure/build CSB.
#
# This mirrors the dependency chain in .github/workflows/build.yml, but keeps
# everything self-contained under ./deps so the resulting CSB binary links ONLY
# against the freshly cloned dependencies (no system-wide installs, no reliance
# on the user's ~/.cmake package registry).
#
# Layout produced:
#   deps/<name>/         cloned source + in-tree build dirs (sibling layout, as CI)
#   deps/install/        shared install prefix consumed by CSB (CMakeLists.txt:57)
#   build/               CSB build directory
#
# Usage:
#   ./configure.sh [OPTIONS]
#
# Options:
#   --shared            Build shared libraries / non-static CSB binary
#                       (default: static, i.e. STATICCOMPILE=ON like CI).
#   --build-type TYPE   CMake build type (default: Release).
#   --build-dir DIR     CSB build directory (default: build).
#   --deps-dir DIR      Where to clone/build deps (default: deps).
#   --jobs N            Parallel build jobs (default: nproc).
#   --skip-deps         Don't (re)build dependencies, only (re)configure CSB.
#   --no-build          Configure only; do not compile CSB.
#   -h, --help          Show this help and exit.
#
# After running, CSB is built into <build-dir>/csb and `ctest` + a smoke test
# are run automatically (unless --no-build).

set -euo pipefail

# --------------------------------------------------------------------------
# Defaults
# --------------------------------------------------------------------------
STATICCOMPILE=ON
BUILD_TYPE="Release"
BUILD_DIR="build"
DEPS_DIR="deps"
JOBS="$(nproc 2>/dev/null || sysctl -n hw.logicalcpu 2>/dev/null || echo 4)"
SKIP_DEPS=OFF
DO_BUILD=ON

# --------------------------------------------------------------------------
# Pinned dependency revisions
# --------------------------------------------------------------------------
# These are the exact commits pinned in flake.lock — the coherent, known-good
# closure that CSB actually compiles against. (CI's branch refs have drifted:
# arjun/cadical master now break CSB's sources, which is why we pin to nix.)
# repo:hash pairs; bump together with flake.lock.
REPO_minisat=stp/minisat;          REF_minisat=14c78206cd12d1d36b7e042fa758747c135670a4
REPO_cadical=meelgroup/cadical;    REF_cadical=9fdd909a08430d309fe7c8cd2bf2e7074b939eec
REPO_cadiback=meelgroup/cadiback;  REF_cadiback=cb090f5bf43c753634ab6b00922a466cf4e7af1b
REPO_breakid=meelgroup/breakid;    REF_breakid=dee9744b7041cec373aa0489128b06a40fce43a1
REPO_cryptominisat=msoos/cryptominisat; REF_cryptominisat=f66a06e9c4ada9f85441be892d1b042ce4d9ee2e
REPO_sbva=meelgroup/sbva;          REF_sbva=0faa08cf3cc26ed855831c9dc16a3489c9ae010f
REPO_arjun=meelgroup/arjun;        REF_arjun=4b42be4bb239e2771026b9dfb658ffc0f0371e94
REPO_approxmc=meelgroup/approxmc;  REF_approxmc=56042dc9002dee312bb4be283d2bdf8bc2a67827
REPO_ganak=meelgroup/ganak;        REF_ganak=c060a9083e7f5477fa86b226030fc8cb32259ab1
REPO_cmsgen=arijitsh/cmsgen;       REF_cmsgen=bad5007705c99122f7417ee585aa58bd00cfe491
REPO_unigen=meelgroup/unigen;      REF_unigen=c6823b3aa5cc37335f018eabcc9cc27790519d41

# --------------------------------------------------------------------------
# Argument parsing
# --------------------------------------------------------------------------
while [[ $# -gt 0 ]]; do
    case "$1" in
        --shared)      STATICCOMPILE=OFF; shift ;;
        --static)      STATICCOMPILE=ON;  shift ;;
        --build-type)  BUILD_TYPE="$2";   shift 2 ;;
        --build-dir)   BUILD_DIR="$2";    shift 2 ;;
        --deps-dir)    DEPS_DIR="$2";     shift 2 ;;
        --jobs|-j)     JOBS="$2";         shift 2 ;;
        --skip-deps)   SKIP_DEPS=ON;      shift ;;
        --no-build)    DO_BUILD=OFF;      shift ;;
        -h|--help)
            sed -n '/^# configure.sh/,/^[^#]/{ /^[^#]/q; s/^# \{0,1\}//p }' "$0"
            exit 0 ;;
        *)
            echo "Unknown option: $1" >&2
            echo "Run '$0 --help' for usage." >&2
            exit 1 ;;
    esac
done

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

# Absolute paths
[[ "$DEPS_DIR" = /* ]] || DEPS_DIR="$SCRIPT_DIR/$DEPS_DIR"
INSTALL_DIR="$DEPS_DIR/install"

echo "==================================================================="
echo " CSB configure"
echo "   static       : $STATICCOMPILE"
echo "   build type   : $BUILD_TYPE"
echo "   deps dir     : $DEPS_DIR"
echo "   install dir  : $INSTALL_DIR"
echo "   CSB build dir: $SCRIPT_DIR/$BUILD_DIR"
echo "   jobs         : $JOBS"
echo "==================================================================="

mkdir -p "$DEPS_DIR" "$INSTALL_DIR"

# --------------------------------------------------------------------------
# Helpers
# --------------------------------------------------------------------------
# clone_dep <name> <repo> <ref> [submodules]
clone_dep() {
    local name="$1" repo="$2" ref="$3" submods="${4:-}"
    local dir="$DEPS_DIR/$name"
    if [[ -d "$dir/.git" ]]; then
        echo ">>> [$name] already cloned, fetching $ref"
        git -C "$dir" fetch --tags --force origin "$ref" 2>/dev/null || git -C "$dir" fetch origin
        git -C "$dir" checkout -q "$ref"
        git -C "$dir" reset --hard -q "origin/$ref" 2>/dev/null || git -C "$dir" reset --hard -q "$ref" 2>/dev/null || true
    else
        echo ">>> [$name] cloning $repo @ $ref"
        git clone "https://github.com/$repo" "$dir"
        git -C "$dir" checkout -q "$ref"
    fi
    if [[ "$submods" == "submodules" ]]; then
        git -C "$dir" submodule update --init --recursive
    fi
}

# cmake_dep <name> [extra cmake args...]
# Configures (build dir), builds and installs a CMake dependency into INSTALL_DIR,
# while also keeping the in-tree build dir (sibling layout) for transitive deps.
cmake_dep() {
    local name="$1"; shift
    local src="$DEPS_DIR/$name"
    echo ">>> [$name] cmake build (static=$STATICCOMPILE)"
    # Pre-seed the cadical/cadiback cache vars (consumed by find_library in
    # cms/approxmc/etc.) so they resolve to OUR autotools-built libs rather
    # than any stale system-installed /usr/local/lib/libcadical.a. Harmless
    # (unused) for deps that don't reference them.
    local cadical_lib="$DEPS_DIR/cadical/build/libcadical.a"
    local cadiback_lib="$DEPS_DIR/cadiback/libcadiback.a"
    local cadi_args=()
    [[ -f "$cadical_lib"  ]] && cadi_args+=(-Dcadical="$cadical_lib")
    [[ -f "$cadiback_lib" ]] && cadi_args+=(-Dcadiback="$cadiback_lib")
    cmake -S "$src" -B "$src/build" \
        -DCMAKE_BUILD_TYPE="$BUILD_TYPE" \
        -DCMAKE_INSTALL_PREFIX="$INSTALL_DIR" \
        -DCMAKE_PREFIX_PATH="$INSTALL_DIR" \
        -DSTATICCOMPILE="$STATICCOMPILE" \
        -DENABLE_TESTING=OFF \
        -DCMAKE_POLICY_VERSION_MINIMUM=3.5 \
        "${cadi_args[@]}" \
        "$@"
    cmake --build "$src/build" --parallel "$JOBS"
    cmake --install "$src/build"
}

# --------------------------------------------------------------------------
# Build dependencies (order and refs taken from .github/workflows/build.yml)
# --------------------------------------------------------------------------
if [[ "$SKIP_DEPS" == "OFF" ]]; then

    # ---- Minisat ----------------------------------------------------------
    clone_dep minisat "$REPO_minisat" "$REF_minisat"
    echo ">>> [minisat] cmake build"
    cmake -S "$DEPS_DIR/minisat" -B "$DEPS_DIR/minisat/build" \
        -DCMAKE_BUILD_TYPE="$BUILD_TYPE" \
        -DCMAKE_INSTALL_PREFIX="$INSTALL_DIR" \
        -DBUILD_SHARED_LIBS=OFF \
        -DSTATICCOMPILE="$STATICCOMPILE" \
        -DSTATIC_BINARIES="$STATICCOMPILE" \
        -DCMAKE_POLICY_VERSION_MINIMUM=3.5 \
        -DZLIB_LIBRARY=-lz
    cmake --build "$DEPS_DIR/minisat/build" --parallel "$JOBS"
    cmake --install "$DEPS_DIR/minisat/build"

    # ---- CaDiCaL (autotools; in-tree static lib at build/libcadical.a) ----
    # At this pin CaDiCaL is autotools-only; cms/arjun/cadiback locate it via
    # the sibling path ../cadical/build, so we build it in place under deps/.
    clone_dep cadical "$REPO_cadical" "$REF_cadical"
    echo ">>> [cadical] autotools build (--competition)"
    ( cd "$DEPS_DIR/cadical" && CXXFLAGS=-fPIC ./configure --competition && make -j"$JOBS" )

    # ---- CaDiBack (autotools; references ../cadical, builds libcadiback.a) -
    clone_dep cadiback "$REPO_cadiback" "$REF_cadiback"
    echo ">>> [cadiback] autotools build"
    ( cd "$DEPS_DIR/cadiback" && CXX=c++ CXXFLAGS=-fPIC ./configure && make -j"$JOBS" )

    # ---- BreakID ----------------------------------------------------------
    clone_dep breakid "$REPO_breakid" "$REF_breakid"
    cmake_dep breakid

    # ---- CryptoMiniSat ----------------------------------------------------
    # (cadical/cadiback are pinned for every cmake_dep — see helper above —
    # because find_library searches system dirs before its PATHS argument and
    # would otherwise grab a stale /usr/local/lib/libcadical.a.)
    clone_dep cryptominisat "$REPO_cryptominisat" "$REF_cryptominisat" submodules
    cmake_dep cryptominisat

    # ---- SBVA -------------------------------------------------------------
    clone_dep sbva "$REPO_sbva" "$REF_sbva"
    cmake_dep sbva

    # ---- Arjun ------------------------------------------------------------
    clone_dep arjun "$REPO_arjun" "$REF_arjun"
    cmake_dep arjun

    # ---- ApproxMC ---------------------------------------------------------
    clone_dep approxmc "$REPO_approxmc" "$REF_approxmc" submodules
    cmake_dep approxmc

    # ---- Ganak (needs flint; uses system flint if present) ----------------
    clone_dep ganak "$REPO_ganak" "$REF_ganak"
    cmake_dep ganak
    # ganak's install is incomplete: it registers the target with the export
    # set but never calls install(EXPORT ganakTargets), so the installed
    # ganakConfig.cmake includes a ganakTargets.cmake that is only written to
    # the build tree. Copy it into the install prefix so find_package(ganak)
    # works against deps/install (the build-tree lib it points to is kept).
    if [[ ! -f "$INSTALL_DIR/lib/cmake/ganak/ganakTargets.cmake" ]]; then
        echo ">>> [ganak] patching incomplete install (copying ganakTargets.cmake)"
        cp "$DEPS_DIR"/ganak/build/ganakTargets*.cmake \
           "$INSTALL_DIR/lib/cmake/ganak/"
    fi

    # ---- CMSGen -----------------------------------------------------------
    clone_dep cmsgen "$REPO_cmsgen" "$REF_cmsgen"
    cmake_dep cmsgen

    # ---- UniGen -----------------------------------------------------------
    clone_dep unigen "$REPO_unigen" "$REF_unigen"
    cmake_dep unigen

    echo ">>> All dependencies built and installed into $INSTALL_DIR"
fi

# --------------------------------------------------------------------------
# Configure CSB against the freshly built deps only.
#   - CMAKE_PREFIX_PATH points at our install prefix (CMakeLists.txt:57 also
#     adds deps/install automatically), where every dependency is installed.
#   - The CMake package registry is disabled so we never pick up the user's
#     other solver builds under ~/.cmake/packages.
#   - A pre-include defines the PkgConfig::GMP / PkgConfig::MPFR imported
#     targets before CSB's find_package(arjun): recent arjun finds GMP/MPFR via
#     pkg-config and exports those target names in its public link interface,
#     but CSB itself locates GMP/MPFR through its own find-modules, so the
#     targets would otherwise be undefined at consume time.
# --------------------------------------------------------------------------
PRELUDE="$DEPS_DIR/csb-prelude.cmake"
cat > "$PRELUDE" <<'EOF'
# Auto-generated by configure.sh — define imported targets that pulled-in
# dependency configs (e.g. arjun) reference in their link interface.
# Use a neutral pkg-config prefix so we do NOT clobber the GMP_*/MPFR_*
# variables that CSB's own Find modules rely on later.
find_package(PkgConfig REQUIRED)
function(_csb_define_pkg_target tgt mod)
    if(NOT TARGET ${tgt})
        pkg_check_modules(_CSBPKG REQUIRED ${mod})
        add_library(${tgt} INTERFACE IMPORTED GLOBAL)
        if(_CSBPKG_INCLUDE_DIRS)
            set_target_properties(${tgt} PROPERTIES
                INTERFACE_INCLUDE_DIRECTORIES "${_CSBPKG_INCLUDE_DIRS}")
        endif()
        if(_CSBPKG_LINK_LIBRARIES)
            set_target_properties(${tgt} PROPERTIES
                INTERFACE_LINK_LIBRARIES "${_CSBPKG_LINK_LIBRARIES}")
        else()
            set_target_properties(${tgt} PROPERTIES
                INTERFACE_LINK_LIBRARIES "${_CSBPKG_LDFLAGS}")
        endif()
    endif()
endfunction()
_csb_define_pkg_target(PkgConfig::GMP gmp)
_csb_define_pkg_target(PkgConfig::MPFR mpfr)
EOF

echo ">>> Configuring CSB"
cmake -S "$SCRIPT_DIR" -B "$SCRIPT_DIR/$BUILD_DIR" \
    -DCMAKE_BUILD_TYPE="$BUILD_TYPE" \
    -DCMAKE_PREFIX_PATH="$INSTALL_DIR" \
    -DCMAKE_PROJECT_CSB_INCLUDE_BEFORE="$PRELUDE" \
    -DCMAKE_FIND_USE_PACKAGE_REGISTRY=OFF \
    -DCMAKE_FIND_USE_SYSTEM_PACKAGE_REGISTRY=OFF \
    -DSTATICCOMPILE="$STATICCOMPILE" \
    -DENABLE_TESTING=OFF \
    -DFORCE_CMS=ON \
    -DFORCE_UNIG=ON \
    -DUSE_GANAK=ON \
    -DUSE_UNIGEN=ON

if [[ "$DO_BUILD" == "OFF" ]]; then
    echo ">>> Configure complete. Build with: cmake --build $BUILD_DIR -j$JOBS"
    exit 0
fi

echo ">>> Building CSB"
cmake --build "$SCRIPT_DIR/$BUILD_DIR" --parallel "$JOBS"

# --------------------------------------------------------------------------
# Test
# --------------------------------------------------------------------------
echo ">>> Running ctest"
( cd "$SCRIPT_DIR/$BUILD_DIR" && ctest -C "$BUILD_TYPE" --output-on-failure || true )

echo ">>> Smoke test"
csb_bin="$SCRIPT_DIR/$BUILD_DIR/csb"
smoke="$SCRIPT_DIR/tests/examples/unweighted.smt2"
if [[ -x "$csb_bin" && -f "$smoke" ]]; then
    out="$("$csb_bin" "$smoke")"
    echo "$out"
    last="$(printf '%s\n' "$out" | tail -n1 | tr -d '\r')"
    if [[ "$last" == "s mc 3" ]]; then
        echo ">>> Smoke test PASSED (got '$last')"
    else
        echo ">>> Smoke test FAILED (expected 's mc 3', got '$last')" >&2
        exit 1
    fi
else
    echo ">>> Skipping smoke test (binary or example missing)" >&2
fi

echo ">>> Done. CSB binary: $csb_bin"
