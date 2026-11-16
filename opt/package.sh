#!/usr/bin/env bash
#
# Build a relocatable binary package of PAL:
#
#   pal-<version>-<commit>-<os>-<arch>/
#     bin/pal                  RUNPATH $ORIGIN/../lib (bundled mode)
#     lib/                     clang-cpp, LLVM and their non-base deps (bundled)
#     lib/clang/<N>/include    clang builtin headers (bundled)
#     include/pal.h            annotation macros
#     pulse/                   the Pulse support library (+ _cache with --check-pulse)
#     share/pal/run-fstar.sh   fstar.exe (or $PAL_FSTAR_EXE) with pulse/ included
#     BUILDINFO
#
# In bundled mode, clang finds its resource directory relative to the
# libclang-cpp that PAL loads (cpp/impl.cpp getResourcesPath), so shipping the
# library in lib/ and the headers in lib/clang/<N> keeps the package
# relocatable. In system mode, the package needs libclang-cpp<N> installed.
#
# Usage: opt/package.sh [--out DIR] [--llvm bundled|system] [--check-pulse]
#                       [--allow-dirty]
# Environment: LLVM_CONFIG, FSTAR_EXE (for --check-pulse), CARGO.

set -euo pipefail

usage() { sed -n '3,21p' "$0" | sed 's/^# \{0,1\}//'; exit "${1:-0}"; }

OUT=dist
LLVM_MODE=bundled
CHECK_PULSE=0
ALLOW_DIRTY=0
while [[ $# -gt 0 ]]; do
    case "$1" in
        --out) OUT="$2"; shift 2 ;;
        --llvm) LLVM_MODE="$2"; shift 2 ;;
        --check-pulse) CHECK_PULSE=1; shift ;;
        --allow-dirty) ALLOW_DIRTY=1; shift ;;
        -h|--help) usage ;;
        *) echo "unknown option: $1" >&2; usage 2 ;;
    esac
done
[[ "$LLVM_MODE" == bundled || "$LLVM_MODE" == system ]] ||
    { echo "--llvm must be bundled or system" >&2; exit 2; }

die() { echo "package.sh: $*" >&2; exit 1; }

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

[[ "$(uname -s)" == Linux ]] || die "only Linux is supported for now"
for tool in patchelf tar sha256sum ldd; do
    command -v "$tool" >/dev/null || die "missing tool: $tool"
done

LLVM_CONFIG="${LLVM_CONFIG:-$(command -v llvm-config-20 || command -v llvm-config || true)}"
[[ -n "$LLVM_CONFIG" ]] || die "llvm-config not found (set LLVM_CONFIG)"
LLVM_VERSION="$("$LLVM_CONFIG" --version)"
LLVM_MAJOR="${LLVM_VERSION%%.*}"
LLVM_LIBDIR="$("$LLVM_CONFIG" --libdir)"

REV="$(git rev-parse HEAD)"
DIRTY=""
if [[ -n "$(git status --porcelain --untracked-files=no)" ]]; then
    [[ $ALLOW_DIRTY == 1 ]] || die "working tree is dirty (--allow-dirty to package anyway)"
    DIRTY="-dirty"
fi
VERSION="$(sed -n 's/^version *= *"\(.*\)"/\1/p' Cargo.toml | head -1)"
NAME="pal-${VERSION}-${REV:0:7}${DIRTY}-linux-$(uname -m)"
mkdir -p "$OUT"
OUT="$(cd "$OUT" && pwd)"
STAGE="$OUT/$NAME"
rm -rf "$STAGE" "$STAGE.tar.gz" "$STAGE.tar.gz.sha256"
mkdir -p "$STAGE"/{bin,lib,include,pulse,share/pal}

echo "== building pal (release)"
LLVM_CONFIG_PATH="$(dirname "$LLVM_CONFIG")"
PATH="$LLVM_CONFIG_PATH:$PATH" "${CARGO:-cargo}" build --release --locked
install -m 755 "${CARGO_TARGET_DIR:-target}/release/pal" "$STAGE/bin/pal"
strip "$STAGE/bin/pal"

# Libraries that every target system provides; everything else that pal
# (transitively) loads is copied into lib/.
is_base_lib() {
    case "$1" in
        linux-vdso.so*|ld-linux*|libc.so*|libm.so*|libdl.so*|libpthread.so*|\
        librt.so*|libutil.so*|libresolv.so*|libstdc++.so*|libgcc_s.so*) return 0 ;;
        *) return 1 ;;
    esac
}

if [[ "$LLVM_MODE" == bundled ]]; then
    echo "== bundling shared libraries"
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

    echo "== bundling clang resource headers"
    RESOURCE_DIR=""
    for cand in "$LLVM_LIBDIR/clang/$LLVM_MAJOR" "$LLVM_LIBDIR/clang/$LLVM_VERSION"; do
        [[ -f "$cand/include/stddef.h" ]] && { RESOURCE_DIR="$cand"; break; }
    done
    [[ -n "$RESOURCE_DIR" ]] || die "clang resource headers not found under $LLVM_LIBDIR/clang"
    mkdir -p "$STAGE/lib/clang/$LLVM_MAJOR"
    cp -rL "$RESOURCE_DIR/include" "$STAGE/lib/clang/$LLVM_MAJOR/include"
fi

echo "== staging the Pulse library and headers"
cp pulse/*.fst pulse/*.fsti pulse/Makefile pulse/fstar.include "$STAGE/pulse/"
cp examples/pal.h "$STAGE/include/pal.h"
cp LICENSE README.md palow.md "$STAGE/"
cat > "$STAGE/share/pal/run-fstar.sh" <<'EOF'
#!/usr/bin/env bash
# fstar.exe with this package's Pulse support library on the include path.
PAL_HOME="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
exec "${PAL_FSTAR_EXE:-fstar.exe}" $OTHERFLAGS \
    --include "$PAL_HOME/pulse" --include "$PAL_HOME/pulse/_cache" "$@"
EOF
chmod 755 "$STAGE/share/pal/run-fstar.sh"

FSTAR_INFO="not checked (run: make -C pulse FSTAR_EXE=<fstar.exe>)"
if [[ $CHECK_PULSE == 1 ]]; then
    echo "== checking the Pulse library"
    FSTAR_EXE="${FSTAR_EXE:-$(command -v fstar.exe || true)}"
    [[ -x "$FSTAR_EXE" ]] || die "fstar.exe not found (set FSTAR_EXE)"
    make --no-print-directory -C "$STAGE/pulse" FSTAR_EXE="$FSTAR_EXE" -j"$(nproc)"
    rm -f "$STAGE/pulse/.depend"
    sha256sum < "$FSTAR_EXE" > "$STAGE/pulse/_cache/.fstar-exe.sha256"
    FSTAR_INFO="$("$FSTAR_EXE" --version | head -1), sha256 $(cut -d' ' -f1 "$STAGE/pulse/_cache/.fstar-exe.sha256")"
fi

cat > "$STAGE/BUILDINFO" <<EOF
pal_version: $VERSION
pal_commit: $REV$DIRTY
llvm: $LLVM_VERSION ($LLVM_MODE)
rustc: $(rustc --version)
glibc: $(ldd --version | head -1 | awk '{ print $NF }')
pulse_cache: $FSTAR_INFO
EOF

echo "== creating archive"
MTIME="$(git log -1 --format=%ct)"
tar --sort=name --owner=0 --group=0 --numeric-owner --mtime="@$MTIME" \
    -C "$OUT" -czf "$STAGE.tar.gz" "$NAME"
(cd "$OUT" && sha256sum "$NAME.tar.gz" > "$NAME.tar.gz.sha256")
rm -rf "$STAGE"
echo "$STAGE.tar.gz"
