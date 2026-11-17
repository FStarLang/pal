#!/usr/bin/env bash
#
# Smoke-test a package built by opt/package.sh, outside the source tree:
# unpack it, check that a bundled package loads no LLVM library from the
# system, translate some tests with the packaged pal, and verify them with the
# packaged Pulse library if fstar.exe is available (VERIFY=0 to skip, VERIFY=1
# to require it). A shipped pulse/_cache checked by another F* is re-checked.
#
# Usage: opt/package-test.sh <pal-*.tar.gz|pal-*.zip> [test...]
# Environment: VERIFY (auto|0|1), FSTAR_EXE (default: fstar.exe on PATH).

set -euo pipefail

[[ $# -ge 1 ]] || { echo "usage: $0 <archive> [test...]" >&2; exit 2; }
ARCHIVE="$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"
shift
if [[ $# -gt 0 ]]; then
    TESTS=("$@")
else
    TESTS=(swap array_alloc bitfields bool_cast break_continue)
fi

fail() { echo "FAIL: $*" >&2; exit 1; }
sha256() { if command -v sha256sum >/dev/null; then sha256sum; else shasum -a 256; fi; }
NPROC="$(nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 2)"

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
TMP="$(cd "$TMP" && pwd -P)"

case "$ARCHIVE" in
    *.zip) unzip -q "$ARCHIVE" -d "$TMP" ;;
    *) tar -xzf "$ARCHIVE" -C "$TMP" ;;
esac
PKG="$(echo "$TMP"/pal-*/)"
PKG="${PKG%/}"
echo "== unpacked to $PKG"
cat "$PKG/BUILDINFO"
BUNDLED=0
grep -q '(bundled)' "$PKG/BUILDINFO" && BUNDLED=1

# The environment the tests run in: on Windows, drop the MSYS2 environment's
# bin directory (where the build found its DLLs) from PATH.
TEST_PATH="$PATH"
EXE=pal
case "$(uname -s)" in
    MINGW*|MSYS*|CYGWIN*)
        EXE=pal.exe
        [[ -n "${MINGW_PREFIX:-}" ]] &&
            TEST_PATH="$(tr ':' '\n' <<<"$PATH" | grep -vxF "$MINGW_PREFIX/bin" | paste -sd: -)" ;;
esac

echo "== shared libraries"
case "$(uname -s)" in
    Linux)
        LIBS="$(ldd "$PKG/bin/pal")"
        echo "$LIBS"
        ! grep -q 'not found' <<<"$LIBS" || fail "unresolved libraries" ;;
    Darwin)
        if [[ $BUNDLED == 1 ]]; then
            for f in "$PKG/bin/pal" "$PKG"/lib/*.dylib; do
                # Every dependency is either part of the OS or found via @rpath.
                bad="$(otool -L "$f" | tail -n +2 | awk '{ print $1 }' |
                    grep -vE '^(@rpath/|/usr/lib/|/System/)' || true)"
                [[ -z "$bad" ]] || fail "$f references $bad"
                codesign -v "$f" || fail "$f: invalid signature"
            done
        fi
        LIBS="$(DYLD_PRINT_LIBRARIES=1 "$PKG/bin/pal" --help 2>&1 >/dev/null | grep -i dylib || true)"
        echo "$LIBS" ;;
    *)
        LIBS="$(PATH="$TEST_PATH" ldd "$PKG/bin/$EXE")"
        echo "$LIBS"
        ! grep -qE 'not found|\?\?\?' <<<"$LIBS" || fail "unresolved libraries" ;;
esac
if [[ $BUNDLED == 1 ]]; then
    outside="$(grep -iE 'lib(clang-cpp|LLVM)' <<<"$LIBS" | grep -viF "$PKG/" || true)"
    [[ -z "$outside" ]] || fail "bundled package loads LLVM from outside the package: $outside"
    grep -iqE 'lib(clang-cpp|LLVM)' <<<"$LIBS" || fail "LLVM libraries not found in the load list"
fi
PATH="$TEST_PATH" "$PKG/bin/$EXE" --help >/dev/null

VERIFY="${VERIFY:-auto}"
FSTAR_BIN="$(command -v "${FSTAR_EXE:-fstar.exe}" || true)"
if [[ "$VERIFY" == auto ]]; then
    [[ -n "$FSTAR_BIN" ]] && VERIFY=1 || VERIFY=0
fi
if [[ "$VERIFY" == 1 ]]; then
    [[ -n "$FSTAR_BIN" ]] || fail "VERIFY=1 but no fstar.exe"
    stamp="$PKG/pulse/_cache/.fstar-exe.sha256"
    if [[ -f "$stamp" && "$(cat "$stamp")" != "$(sha256 < "$FSTAR_BIN")" ]]; then
        echo "== the shipped Pulse cache was checked by another F*; discarding it"
        rm -rf "$PKG/pulse/_cache"
    fi
    if [[ ! -f "$stamp" ]]; then
        echo "== checking the packaged Pulse library"
        make --no-print-directory -C "$PKG/pulse" -j"$NPROC" FSTAR_EXE="$FSTAR_BIN"
    fi
fi

# The test Makefiles take the translator and F* as parameters; copy the tests
# so that nothing is written to (or read from) the source tree's build output.
mkdir -p "$TMP/test"
cp "$ROOT/test/verify.mk" "$TMP/test/"
status=0
for t in "${TESTS[@]}"; do
    cp -RL "$ROOT/test/$t" "$TMP/test/$t"
    rm -rf "$TMP/test/$t"/{out,_cache,obj}
    # Exercise the packaged annotation header, not the test's copy.
    rm -f "$TMP/test/$t/pal.h"
    cp "$PKG/include/pal.h" "$TMP/test/$t/pal.h"
    target=translate
    [[ "$VERIFY" == 1 ]] && target=verify
    echo "== $t: $target"
    # A minimal environment, except on Windows where native programs need
    # SYSTEMROOT, TEMP, etc.
    case "$(uname -s)" in
        Linux|Darwin) run=(env -i PATH="$TEST_PATH" HOME="$TMP" PAL_FSTAR_EXE="$FSTAR_BIN") ;;
        *) run=(env PATH="$TEST_PATH" PAL_FSTAR_EXE="$FSTAR_BIN") ;;
    esac
    if "${run[@]}" make --no-print-directory -C "$TMP/test/$t" "$target" \
            C2PULSE="$PKG/bin/$EXE" FSTAR_EXE="$PKG/share/pal/run-fstar.sh"; then
        echo "PASS: $t"
    else
        echo "FAIL: $t" >&2; status=1
    fi
done
exit $status
