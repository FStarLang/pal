#!/usr/bin/env bash
#
# Build a relocatable binary package of PAL for Linux, macOS or Windows (MSYS2
# UCRT64):
#
#   pal-<version>-<commit>-<os>-<arch>/
#     bin/pal[.exe]            the translator
#     lib/                     clang-cpp, LLVM and their non-base deps (bundled;
#                              on Windows the DLLs are in bin/ instead)
#     lib/clang/<N>/include    clang builtin headers (bundled)
#     include/pal.h            annotation macros
#     pulse/                   the Pulse support library (+ _cache with --check-pulse)
#     fstar/                   F* and z3 (with --fstar): fstar.exe, its standard
#                              and Pulse libraries, and F*'s default z3
#     share/pal/run-fstar.sh   F* ($PAL_FSTAR_EXE, else the bundled one, else
#                              fstar.exe on PATH) with pulse/ included
#     share/pal/run-fstar.cmd  the same, for cmd.exe/PowerShell (Windows)
#     BUILDINFO
#
# Clang finds its resource directory relative to the libclang-cpp that PAL
# loads (Linux, macOS) or to pal.exe (Windows) (cpp/impl.cpp getResourcesPath),
# so the package is relocatable. In system mode, the package needs the build
# host's libclang-cpp<N> installed instead.
#
# Usage: opt/package.sh [--out DIR] [--llvm bundled|system] [--check-pulse]
#                       [--fstar DIR [--fstar-z3 VER,...|all]] [--allow-dirty]
#   --fstar DIR   bundle the F* binary distribution installed in DIR (e.g. by
#                 opt/install-fstar.sh --dest DIR), and check pulse/ with it
#   --fstar-z3    the z3 versions to bundle (default: F*'s default version)
# Environment: LLVM_CONFIG, FSTAR_EXE (for --check-pulse without --fstar),
#   CARGO, FSTAR_LIB_PATH (macOS: directories where to find the dylibs that
#   fstar.exe links, by name, if they are not where it says, e.g. for an
#   F* of another architecture that runs under Rosetta 2).
# Output: dist/<name>.tar.gz (Linux, macOS) or .zip (Windows), and .sha256.

set -euo pipefail

usage() { sed -n '3,35p' "$0" | sed 's/^# \{0,1\}//'; exit "${1:-0}"; }

OUT=dist
LLVM_MODE=bundled
CHECK_PULSE=0
ALLOW_DIRTY=0
FSTAR_DIR=""
FSTAR_Z3=default
while [[ $# -gt 0 ]]; do
    case "$1" in
        --out) OUT="$2"; shift 2 ;;
        --llvm) LLVM_MODE="$2"; shift 2 ;;
        --check-pulse) CHECK_PULSE=1; shift ;;
        --allow-dirty) ALLOW_DIRTY=1; shift ;;
        --fstar) FSTAR_DIR="$2"; shift 2 ;;
        --fstar-z3) FSTAR_Z3="$2"; shift 2 ;;
        -h|--help) usage ;;
        *) echo "unknown option: $1" >&2; usage 2 ;;
    esac
done
[[ "$LLVM_MODE" == bundled || "$LLVM_MODE" == system ]] ||
    { echo "--llvm must be bundled or system" >&2; exit 2; }

die() { echo "package.sh: $*" >&2; exit 1; }

if [[ -n "$FSTAR_DIR" ]]; then
    FSTAR_DIR="$(cd "$FSTAR_DIR" && pwd)" || die "no such directory: $FSTAR_DIR"
    [[ -f "$FSTAR_DIR/bin/fstar.exe" ]] || die "$FSTAR_DIR/bin/fstar.exe not found"
    CHECK_PULSE=1
fi

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

EXE=pal
ARCH="$(uname -m)"
case "$(uname -s)" in
    Linux) OS=linux; TOOLS="patchelf tar ldd" ;;
    Darwin) OS=macos; TOOLS="otool install_name_tool codesign tar" ;;
    MINGW*|MSYS*|CYGWIN*)
        OS=windows; EXE=pal.exe; TOOLS="ldd zip"
        [[ -n "${MINGW_PREFIX:-}" ]] || die "run from an MSYS2 UCRT64 shell (MINGW_PREFIX is unset)" ;;
    *) die "unsupported OS: $(uname -s)" ;;
esac
for tool in $TOOLS; do
    command -v "$tool" >/dev/null || die "missing tool: $tool"
done

sha256() { if command -v sha256sum >/dev/null; then sha256sum "$@"; else shasum -a 256 "$@"; fi; }
NPROC="$(nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 2)"

LLVM_CONFIG="${LLVM_CONFIG:-$(command -v llvm-config-23 || command -v llvm-config || true)}"
[[ -n "$LLVM_CONFIG" ]] || die "llvm-config not found (set LLVM_CONFIG)"
LLVM_VERSION="$("$LLVM_CONFIG" --version | tr -d '\r')"
LLVM_MAJOR="${LLVM_VERSION%%.*}"
LLVM_LIBDIR="$("$LLVM_CONFIG" --libdir | tr -d '\r')"

REV="$(git rev-parse HEAD)"
DIRTY=""
if [[ -n "$(git status --porcelain --untracked-files=no)" ]]; then
    [[ $ALLOW_DIRTY == 1 ]] || die "working tree is dirty (--allow-dirty to package anyway)"
    DIRTY="-dirty"
fi
VERSION="$(sed -n 's/^version *= *"\(.*\)"/\1/p' Cargo.toml | sed -n 1p)"
NAME="pal-${VERSION}-${REV:0:7}${DIRTY}-${OS}-${ARCH}"
mkdir -p "$OUT"
OUT="$(cd "$OUT" && pwd)"
STAGE="$OUT/$NAME"
rm -rf "$STAGE" "$STAGE".tar.gz* "$STAGE".zip*
mkdir -p "$STAGE"/{bin,lib,include,pulse,share/pal}
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

echo "== building pal (release)"
TARGET_DIR="${CARGO_TARGET_DIR:-target}"
if [[ $OS == macos ]]; then
    # build.rs runs `llvm-config` and `clang++` from PATH. Expose only
    # llvm-config, so that Apple's clang++ compiles against the system libc++
    # that pal links with; leave room in the Mach-O header for install_name_tool.
    ln -s "$LLVM_CONFIG" "$WORK/llvm-config"
    PATH="$WORK:$PATH" RUSTFLAGS="${RUSTFLAGS:-} -C link-arg=-Wl,-headerpad_max_install_names" \
        "${CARGO:-cargo}" build --release --locked
else
    PATH="$(dirname "$LLVM_CONFIG"):$PATH" "${CARGO:-cargo}" build --release --locked
fi
install -m 755 "$TARGET_DIR/release/$EXE" "$STAGE/bin/$EXE"
STRIP="$(command -v strip || command -v llvm-strip || true)"
if [[ -n "$STRIP" ]]; then
    if [[ $OS == macos ]]; then "$STRIP" -x "$STAGE/bin/$EXE"; else "$STRIP" "$STAGE/bin/$EXE"; fi
fi

# --- Linux: copy the ldd closure minus the base system, set RUNPATHs. ---------

is_base_lib() {
    case "$1" in
        linux-vdso.so*|ld-linux*|libc.so*|libm.so*|libdl.so*|libpthread.so*|\
        librt.so*|libutil.so*|libresolv.so*|libstdc++.so*|libgcc_s.so*) return 0 ;;
        *) return 1 ;;
    esac
}

bundle_linux() {
    # ldd resolves the full transitive closure; copy each non-base library
    # under its soname.
    while read -r soname path; do
        is_base_lib "$soname" && continue
        [[ -f "$path" ]] || die "unresolved dependency $soname"
        cp -L "$path" "$STAGE/lib/$soname"
        chmod 644 "$STAGE/lib/$soname"
    done < <(ldd "$STAGE/bin/pal" | awk '$2 == "=>" { print $1, $3 }')
    patchelf --set-rpath '$ORIGIN/../lib' "$STAGE/bin/pal"
    for lib in "$STAGE"/lib/*.so*; do
        patchelf --set-rpath '$ORIGIN' "$lib"
    done
    ls "$STAGE"/lib/libclang-cpp.so* >/dev/null 2>&1 || die "libclang-cpp was not bundled"
}

# --- macOS: copy the otool -L closure minus the OS, rewrite install names to --
# --- @rpath/<name>, and ad-hoc sign every modified Mach-O file. --------------

SRC_EXE_DIR="$ROOT/$TARGET_DIR/release"

macho_rpaths() { otool -l "$1" | awk '$1 == "cmd" && $2 == "LC_RPATH" { getline; getline; print $2 }'; }

# Resolve a load command $1 found in the (original, unmodified) file $2.
macho_resolve() {
    local ref="$1" from="$2" dir rp
    dir="$(dirname "$from")"
    case "$ref" in
        @rpath/*)
            while read -r rp; do
                rp="${rp/#@loader_path/$dir}"
                rp="${rp/#@executable_path/$SRC_EXE_DIR}"
                [[ -f "$rp/${ref#@rpath/}" ]] && { echo "$rp/${ref#@rpath/}"; return; }
            done < <(macho_rpaths "$from")
            [[ -f "$LLVM_LIBDIR/${ref#@rpath/}" ]] && { echo "$LLVM_LIBDIR/${ref#@rpath/}"; return; } ;;
        @loader_path/*) [[ -f "$dir/${ref#@loader_path/}" ]] && { echo "$dir/${ref#@loader_path/}"; return; } ;;
        @executable_path/*) [[ -f "$SRC_EXE_DIR/${ref#@executable_path/}" ]] && { echo "$SRC_EXE_DIR/${ref#@executable_path/}"; return; } ;;
        *) [[ -f "$ref" ]] && { echo "$ref"; return; } ;;
    esac
    return 1
}

# Bundle the dependencies of $2 (staged copy of the original file $1).
macho_bundle() {
    local from="$1" staged="$2" deps ref name src
    deps="$(otool -L "$staged" | tail -n +2 | awk '{ print $1 }')"
    while read -r ref; do
        [[ -n "$ref" ]] || continue
        case "$ref" in /usr/lib/*|/System/*) continue ;; esac
        # A dylib's own install name is listed first.
        [[ "$(basename "$ref")" == "$(basename "$staged")" ]] && continue
        src="$(macho_resolve "$ref" "$from")" || die "cannot resolve $ref (from $from)"
        # Name the copy after the library's install name, so that references
        # through different symlinks share a single copy.
        name="$(otool -D "$src" | sed -n 2p)"
        name="$(basename "${name:-$ref}")"
        install_name_tool -change "$ref" "@rpath/$name" "$staged"
        if [[ ! -f "$STAGE/lib/$name" ]]; then
            cp -L "$src" "$STAGE/lib/$name"
            chmod 644 "$STAGE/lib/$name"
            install_name_tool -id "@rpath/$name" "$STAGE/lib/$name"
            macho_bundle "$src" "$STAGE/lib/$name"
        fi
    done <<<"$deps"
}

macho_set_rpath() {
    local rp
    while read -r rp; do
        [[ -n "$rp" ]] && install_name_tool -delete_rpath "$rp" "$1"
    done < <(macho_rpaths "$1")
    install_name_tool -add_rpath "$2" "$1"
}

bundle_macos() {
    macho_bundle "$SRC_EXE_DIR/pal" "$STAGE/bin/pal"
    macho_set_rpath "$STAGE/bin/pal" @executable_path/../lib
    for lib in "$STAGE"/lib/*.dylib; do
        macho_set_rpath "$lib" @loader_path
    done
    # Editing load commands invalidates signatures; arm64 refuses to run
    # unsigned code.
    codesign -f -s - "$STAGE/bin/pal" "$STAGE"/lib/*.dylib
    ls "$STAGE"/lib/libclang-cpp*.dylib >/dev/null 2>&1 || die "libclang-cpp was not bundled"
}

# --- Windows: copy the DLLs that come from the MSYS2 environment next to -----
# --- pal.exe (the exe's directory is searched first). -------------------------

bundle_windows() {
    local mingw_bin
    mingw_bin="$(cd "$MINGW_PREFIX/bin" && pwd -P)"
    while read -r dll path; do
        case "$(cd "$(dirname "$path")" 2>/dev/null && pwd -P)" in
            "$mingw_bin") cp "$path" "$STAGE/bin/$dll" ;;
        esac
    done < <(ldd "$STAGE/bin/pal.exe" | awk '$2 == "=>" { print $1, $3 }')
    ls "$STAGE"/bin/libclang-cpp*.dll >/dev/null 2>&1 || die "libclang-cpp was not bundled"
}

if [[ "$LLVM_MODE" == bundled ]]; then
    echo "== bundling shared libraries"
    "bundle_$OS"

    echo "== bundling clang resource headers"
    RESOURCE_DIR=""
    for cand in "$LLVM_LIBDIR/clang/$LLVM_MAJOR" "$LLVM_LIBDIR/clang/$LLVM_VERSION" \
                "$(clang++ -print-resource-dir 2>/dev/null | tr -d '\r' || true)"; do
        [[ -n "$cand" && -f "$cand/include/stddef.h" ]] && { RESOURCE_DIR="$cand"; break; }
    done
    [[ -n "$RESOURCE_DIR" ]] || die "clang resource headers not found under $LLVM_LIBDIR/clang"
    mkdir -p "$STAGE/lib/clang/$LLVM_MAJOR"
    cp -RL "$RESOURCE_DIR/include" "$STAGE/lib/clang/$LLVM_MAJOR/include"
fi

echo "== staging the Pulse library and headers"
cp pulse/*.fst pulse/*.fsti pulse/Makefile pulse/fstar.include "$STAGE/pulse/"
cp examples/pal.h "$STAGE/include/pal.h"
cp LICENSE README.md palow.md "$STAGE/"
cat > "$STAGE/share/pal/run-fstar.sh" <<'EOF'
#!/usr/bin/env bash
# fstar.exe with this package's Pulse support library on the include path.
PAL_HOME="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
if [[ -z "${PAL_FSTAR_EXE:-}" ]]; then
    PAL_FSTAR_EXE=fstar.exe
    [[ -f "$PAL_HOME/fstar/bin/fstar.exe" ]] && PAL_FSTAR_EXE="$PAL_HOME/fstar/bin/fstar.exe"
fi
exec "$PAL_FSTAR_EXE" $OTHERFLAGS \
    --include "$PAL_HOME/pulse" --include "$PAL_HOME/pulse/_cache" "$@"
EOF
chmod 755 "$STAGE/share/pal/run-fstar.sh"
if [[ $OS == windows ]]; then
    printf '%s\r\n' \
        '@echo off' \
        'rem fstar.exe with this package'"'"'s Pulse support library on the include path.' \
        'setlocal' \
        'set "PAL_HOME=%~dp0..\.."' \
        'if not defined PAL_FSTAR_EXE if exist "%PAL_HOME%\fstar\bin\fstar.exe" set "PAL_FSTAR_EXE=%PAL_HOME%\fstar\bin\fstar.exe"' \
        'if not defined PAL_FSTAR_EXE set "PAL_FSTAR_EXE=fstar.exe"' \
        '"%PAL_FSTAR_EXE%" %OTHERFLAGS% --include "%PAL_HOME%\pulse" --include "%PAL_HOME%\pulse\_cache" %*' \
        > "$STAGE/share/pal/run-fstar.cmd"
fi

# --- F* and z3: only what verification needs (not F*'s OCaml compiler -------
# --- libraries, krml or other z3 versions). -----------------------------------

# macOS: make a prebuilt Mach-O file ($1) self-contained. Copy its non-system
# dylibs next to it and reference them as $2/<name> ($2 = @executable_path for
# an executable, @loader_path for a dylib): shorter than the absolute Homebrew
# paths that F* references, so the load commands are edited in place.
macho_bundle_prebuilt() {
    local file="$1" prefix="$2" dir ref name src d changed=0 dirs=()
    dir="$(dirname "$file")"
    IFS=: read -r -a dirs <<<"${FSTAR_LIB_PATH:-}"
    while read -r ref; do
        case "$ref" in ""|/usr/lib/*|/System/*|@rpath/*|@loader_path/*|@executable_path/*) continue ;; esac
        name="$(basename "$ref")"
        [[ "$name" == "$(basename "$file")" ]] && continue
        src=""
        [[ -f "$ref" ]] && src="$ref"
        if [[ -z "$src" ]]; then
            for d in ${dirs[@]+"${dirs[@]}"}; do
                [[ -f "$d/$name" ]] && { src="$d/$name"; break; }
            done
        fi
        [[ -n "$src" ]] || die "$file links $ref, which is not there (set FSTAR_LIB_PATH)"
        install_name_tool -change "$ref" "$prefix/$name" "$file"
        changed=1
        if [[ ! -f "$dir/$name" ]]; then
            cp -L "$src" "$dir/$name"
            chmod 644 "$dir/$name"
            install_name_tool -id "@loader_path/$name" "$dir/$name"
            macho_bundle_prebuilt "$dir/$name" @loader_path
            codesign -f -s - "$dir/$name"
        fi
    done < <(otool -L "$file" | tail -n +2 | awk '{ print $1 }')
    if [[ $changed == 1 ]]; then codesign -f -s - "$file"; fi
}

FSTAR_BUNDLED=""
if [[ -n "$FSTAR_DIR" ]]; then
    echo "== bundling F* and z3"
    F="$STAGE/fstar"
    mkdir -p "$F/bin" "$F/lib/fstar"
    cp "$FSTAR_DIR/bin/fstar.exe" "$F/bin/"
    if [[ $OS == windows ]]; then
        find "$FSTAR_DIR/bin" -maxdepth 1 -name '*.dll' -exec cp {} "$F/bin/" \;
    fi
    for f in fstar.include ulib ulib.checked pulse; do
        cp -R "$FSTAR_DIR/lib/fstar/$f" "$F/lib/fstar/"
    done
    for f in LICENSE LICENSE-fsharp.txt README.md version.txt; do
        if [[ -f "$FSTAR_DIR/$f" ]]; then cp "$FSTAR_DIR/$f" "$F/"; fi
    done
    [[ $OS == macos ]] && macho_bundle_prebuilt "$F/bin/fstar.exe" @executable_path
    if [[ "$FSTAR_Z3" == default ]]; then
        help="$("$F/bin/fstar.exe" --help | tr -d '\r')"
        FSTAR_Z3="$(awk 'z && /Default:/ { sub(/.*Default: */, ""); print $1; exit }
                         /^--z3version/ { z = 1 }' <<<"$help")"
        [[ -n "$FSTAR_Z3" ]] || die "cannot find F*'s default z3 version"
    elif [[ "$FSTAR_Z3" == all ]]; then
        FSTAR_Z3="$(cd "$FSTAR_DIR/lib/fstar" && for d in z3-*; do echo "${d#z3-}"; done | paste -sd, -)"
    fi
    for v in ${FSTAR_Z3//,/ }; do
        [[ -d "$FSTAR_DIR/lib/fstar/z3-$v" ]] || die "F* has no z3 $v in $FSTAR_DIR/lib/fstar"
        cp -R "$FSTAR_DIR/lib/fstar/z3-$v" "$F/lib/fstar/"
        if [[ $OS == macos ]]; then
            macho_bundle_prebuilt "$F/lib/fstar/z3-$v/bin/z3" @executable_path
        fi
    done
    FSTAR_EXE="$F/bin/fstar.exe"
    FSTAR_BUNDLED="bundled, z3 ${FSTAR_Z3//,/ }"
    if [[ $OS == macos ]]; then
        FSTAR_BUNDLED="$FSTAR_BUNDLED, $(lipo -archs "$FSTAR_EXE")"
        [[ " $(lipo -archs "$FSTAR_EXE") " == *" $ARCH "* ]] ||
            FSTAR_BUNDLED="$FSTAR_BUNDLED (runs under Rosetta 2)"
    fi
fi

FSTAR_INFO="not checked (run: make -C pulse FSTAR_EXE=<fstar.exe>)"
if [[ $CHECK_PULSE == 1 ]]; then
    echo "== checking the Pulse library"
    FSTAR_EXE="${FSTAR_EXE:-$(command -v fstar.exe || true)}"
    [[ -x "$FSTAR_EXE" ]] || die "fstar.exe not found (set FSTAR_EXE)"
    make --no-print-directory -C "$STAGE/pulse" FSTAR_EXE="$FSTAR_EXE" -j"$NPROC"
    rm -f "$STAGE/pulse/.depend"
    sha256 < "$FSTAR_EXE" > "$STAGE/pulse/_cache/.fstar-exe.sha256"
    FSTAR_INFO="$("$FSTAR_EXE" --version | sed -n 1p | tr -d '\r'), sha256 $(cut -d' ' -f1 "$STAGE/pulse/_cache/.fstar-exe.sha256")"
fi

case $OS in
    linux) PLATFORM="glibc $(ldd --version | awk 'NR == 1 { print $NF }')" ;;
    macos) PLATFORM="macOS $(sw_vers -productVersion) (minimum: $(otool -l "$STAGE/bin/pal" |
                awk '$1 == "minos" && !m { m = $2 } END { print m }'); needs the Xcode command line tools)" ;;
    windows) PLATFORM="$MSYSTEM $(uname -r)" ;;
esac
cat > "$STAGE/BUILDINFO" <<EOF
pal_version: $VERSION
pal_commit: $REV$DIRTY
llvm: $LLVM_VERSION ($LLVM_MODE)
rustc: $(rustc --version | tr -d '\r')
platform: $PLATFORM
pulse_cache: $FSTAR_INFO
fstar: ${FSTAR_BUNDLED:-not bundled (needs F* and z3 on PATH or PAL_FSTAR_EXE)}
EOF

echo "== creating archive"
MTIME="$(git log -1 --format=%ct)"
if [[ $OS == windows ]]; then
    ARCHIVE="$NAME.zip"
    find "$STAGE" -exec touch -h -d "@$MTIME" {} +
    (cd "$OUT" && find "$NAME" | LC_ALL=C sort | zip -qX "$ARCHIVE" -@)
elif tar --version 2>/dev/null | grep -q GNU; then
    ARCHIVE="$NAME.tar.gz"
    tar --sort=name --owner=0 --group=0 --numeric-owner --mtime="@$MTIME" \
        -C "$OUT" -czf "$OUT/$ARCHIVE" "$NAME"
else
    ARCHIVE="$NAME.tar.gz"
    tar --uid 0 --gid 0 -C "$OUT" -czf "$OUT/$ARCHIVE" "$NAME"
fi
(cd "$OUT" && sha256 "$ARCHIVE" > "$ARCHIVE.sha256")
rm -rf "$STAGE"
echo "$OUT/$ARCHIVE"
