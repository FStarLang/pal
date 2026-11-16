#!/usr/bin/env bash
#
# Smoke-test a package built by opt/package.sh, outside the source tree:
# unpack it, check that a bundled package loads no LLVM library from the
# system, translate some tests with the packaged pal, and verify them with the
# packaged Pulse library if fstar.exe is available (VERIFY=0 to skip, VERIFY=1
# to require it). A shipped pulse/_cache checked by another F* is re-checked.
#
# Usage: opt/package-test.sh <pal-*.tar.gz> [test...]
# Environment: VERIFY (auto|0|1), FSTAR_EXE (default: fstar.exe on PATH).

set -euo pipefail

[[ $# -ge 1 ]] || { echo "usage: $0 <tarball> [test...]" >&2; exit 2; }
TARBALL="$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"
shift
if [[ $# -gt 0 ]]; then
    TESTS=("$@")
else
    TESTS=(swap array_alloc bitfields bool_cast break_continue)
fi

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

tar -xzf "$TARBALL" -C "$TMP"
PKG="$(echo "$TMP"/pal-*/)"
PKG="${PKG%/}"
echo "== unpacked to $PKG"
cat "$PKG/BUILDINFO"

echo "== shared libraries"
LDD="$(ldd "$PKG/bin/pal")"
echo "$LDD"
if grep -q 'not found' <<<"$LDD"; then
    echo "FAIL: unresolved libraries" >&2; exit 1
fi
if grep -q '(bundled)' "$PKG/BUILDINFO" &&
    grep -E 'lib(clang-cpp|LLVM)' <<<"$LDD" | grep -vqF "$PKG/"; then
    echo "FAIL: bundled package loads LLVM from outside the package" >&2; exit 1
fi
"$PKG/bin/pal" --help >/dev/null

VERIFY="${VERIFY:-auto}"
FSTAR_BIN="$(command -v "${FSTAR_EXE:-fstar.exe}" || true)"
if [[ "$VERIFY" == auto ]]; then
    [[ -n "$FSTAR_BIN" ]] && VERIFY=1 || VERIFY=0
fi
if [[ "$VERIFY" == 1 ]]; then
    [[ -n "$FSTAR_BIN" ]] || { echo "FAIL: VERIFY=1 but no fstar.exe" >&2; exit 1; }
    stamp="$PKG/pulse/_cache/.fstar-exe.sha256"
    if [[ -f "$stamp" && "$(cat "$stamp")" != "$(sha256sum < "$FSTAR_BIN")" ]]; then
        echo "== the shipped Pulse cache was checked by another F*; discarding it"
        rm -rf "$PKG/pulse/_cache"
    fi
    if [[ ! -f "$stamp" ]]; then
        echo "== checking the packaged Pulse library"
        make --no-print-directory -C "$PKG/pulse" -j"$(nproc)" FSTAR_EXE="$FSTAR_BIN"
    fi
fi

# The test Makefiles take the translator and F* as parameters; copy the tests
# so that nothing is written to (or read from) the source tree's build output.
mkdir -p "$TMP/test"
cp "$ROOT/test/verify.mk" "$TMP/test/"
fail=0
for t in "${TESTS[@]}"; do
    cp -rL "$ROOT/test/$t" "$TMP/test/$t"
    rm -rf "$TMP/test/$t"/{out,_cache,obj}
    # Exercise the packaged annotation header, not the test's copy.
    rm -f "$TMP/test/$t/pal.h"
    cp "$PKG/include/pal.h" "$TMP/test/$t/pal.h"
    target=translate
    [[ "$VERIFY" == 1 ]] && target=verify
    echo "== $t: $target"
    if env -i PATH="$PATH" HOME="$TMP" PAL_FSTAR_EXE="$FSTAR_BIN" \
        make --no-print-directory -C "$TMP/test/$t" "$target" \
            C2PULSE="$PKG/bin/pal" FSTAR_EXE="$PKG/share/pal/run-fstar.sh"; then
        echo "PASS: $t"
    else
        echo "FAIL: $t" >&2; fail=1
    fi
done
exit $fail
