#!/usr/bin/env bash
#
# Build an F* binary distribution from the F* sources at a given git ref, the
# way F*'s nightly builds do (make package ADMIT=1), and install it into DIR:
# DIR/bin/fstar.exe and DIR/lib/fstar/{ulib,ulib.checked,pulse,z3-*,...}, the
# layout that opt/install-fstar.sh --dest DIR produces and that
# opt/package.sh --fstar DIR bundles. Linux and macOS only (on Windows, F* is
# built from a source package made on Linux).
#
# Usage: opt/build-fstar.sh --dest DIR (--ref REF [--repo URL] | --src DIR)
#                           [--work DIR] [--jobs N] [--install-deps]
#        opt/build-fstar.sh --print-commit --ref REF [--repo URL]
#   --ref REF       branch, tag or full commit SHA of --repo
#   --repo URL      default: https://github.com/FStarLang/FStar.git
#   --src DIR       build this F* checkout (with its submodules) instead
#   --work DIR      where to clone --repo (default: a temporary directory)
#   --install-deps  first install F*'s OCaml dependencies with opam
#   --print-commit  only print the commit SHA that REF denotes in --repo
# Requirements: git, curl, OCaml (>= 4.14; F*'s builds use 5.3.0) with F*'s
#   opam dependencies (or --install-deps), GNU make (gmake on macOS), and gmp
#   (e.g. on macOS: brew install opam make gmp).
# Environment: FSTAR_VERSION (the version that fstar.exe --version prints,
#   default: git-<12-digit commit>).
# Writes DIR/SOURCE: the repository, ref and commit that F* was built from.

set -euo pipefail

usage() { sed -n '3,25p' "$0" | sed 's/^# \{0,1\}//'; exit "${1:-0}"; }
die() { echo "build-fstar.sh: $*" >&2; exit 1; }

REPO=https://github.com/FStarLang/FStar.git
REF=""
SRC=""
DEST=""
WORK=""
JOBS="$(nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 2)"
INSTALL_DEPS=0
PRINT_COMMIT=0
while [[ $# -gt 0 ]]; do
    case "$1" in
        --ref) REF="$2"; shift 2 ;;
        --repo) REPO="$2"; shift 2 ;;
        --src) SRC="$2"; shift 2 ;;
        --dest) DEST="$2"; shift 2 ;;
        --work) WORK="$2"; shift 2 ;;
        --jobs) JOBS="$2"; shift 2 ;;
        --install-deps) INSTALL_DEPS=1; shift ;;
        --print-commit) PRINT_COMMIT=1; shift ;;
        -h|--help) usage ;;
        *) echo "unknown option: $1" >&2; usage 2 ;;
    esac
done

# The commit that REF denotes in REPO: a full SHA as is, else a branch or tag
# (peeled, for annotated tags).
resolve_commit() {
    if [[ "$REF" =~ ^[0-9a-f]{40}$ ]]; then echo "$REF"; return; fi
    local refs
    refs="$(git ls-remote "$REPO" "$REF" "$REF^{}")" || die "cannot list the refs of $REPO"
    awk '$2 ~ /\^\{\}$/ { peeled = $1 } NR == 1 { first = $1 }
         END { if (peeled) print peeled; else if (first) print first }' <<<"$refs" | grep . ||
        die "no branch or tag $REF in $REPO (give commits as full SHAs)"
}

if [[ $PRINT_COMMIT == 1 ]]; then
    [[ -n "$REF" ]] || die "--print-commit needs --ref"
    resolve_commit
    exit 0
fi

[[ -n "$DEST" ]] || die "--dest is required"
[[ -n "$REF" || -n "$SRC" ]] || die "--ref or --src is required"
[[ -z "$REF" || -z "$SRC" ]] || die "--ref and --src are exclusive"
case "$(uname -s)" in
    Linux) MAKE="make" ;;
    Darwin) MAKE="gmake" ;;
    *) die "unsupported OS: $(uname -s) (Linux and macOS only)" ;;
esac
command -v "$MAKE" >/dev/null || die "missing tool: $MAKE (GNU make)"
for tool in git curl; do
    command -v "$tool" >/dev/null || die "missing tool: $tool"
done
mkdir -p "$DEST"
DEST="$(cd "$DEST" && pwd)"
# DEST is emptied before installing: only if it is empty or an F* install.
[[ -z "$(ls -A "$DEST")" || -f "$DEST/bin/fstar.exe" ]] ||
    die "$DEST is neither empty nor an F* installation"

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

if [[ -n "$REF" ]]; then
    COMMIT="$(resolve_commit)"
    SRC="${WORK:-$TMP}/FStar"
    echo "== fetching F* $REF ($COMMIT) from $REPO"
    rm -rf "$SRC"
    git init -q "$SRC"
    git -C "$SRC" remote add origin "$REPO"
    git -C "$SRC" fetch -q --depth 1 origin "$COMMIT"
    git -C "$SRC" checkout -q --detach FETCH_HEAD
else
    SRC="$(cd "$SRC" && pwd)" || die "no such directory: $SRC"
    REPO="$(git -C "$SRC" remote get-url origin 2>/dev/null || echo "$SRC")"
    REF="$(git -C "$SRC" describe --all --always 2>/dev/null || echo unknown)"
    COMMIT="$(git -C "$SRC" rev-parse HEAD)"
    [[ -z "$(git -C "$SRC" status --porcelain --untracked-files=no)" ]] || COMMIT="$COMMIT-dirty"
fi
[[ -f "$SRC/fstar.opam" ]] || die "$SRC is not an F* source tree"
git -C "$SRC" submodule update -q --init --recursive

# The OCaml switch that opam would select (no-op if already in the environment).
if command -v opam >/dev/null; then eval "$(opam env 2>/dev/null)" || true; fi
if [[ $INSTALL_DEPS == 1 ]]; then
    echo "== installing F*'s OCaml dependencies"
    opam install -y --deps-only "$SRC/fstar.opam"
    eval "$(opam env)"
fi
command -v ocamlfind >/dev/null || command -v dune >/dev/null ||
    die "OCaml and F*'s dependencies not found (opam install --deps-only fstar.opam, or --install-deps)"

echo "== building F* (make package ADMIT=1)"
export FSTAR_VERSION="${FSTAR_VERSION:-git-${COMMIT:0:12}}"
rm -f "$SRC/fstar.tar.gz"
"$MAKE" -C "$SRC" -skj"$JOBS" package ADMIT=1 FSTAR_TAG=

echo "== installing into $DEST"
find "$DEST" -mindepth 1 -delete
mkdir "$TMP/pkg"
tar -xzf "$SRC/fstar.tar.gz" -C "$TMP/pkg"
# The archive's top directory (fstar/ or ./fstar/).
top="$(dirname "$(dirname "$(find "$TMP/pkg" -path '*/bin/fstar.exe' | head -1)")")"
[[ "$top" != . ]] || die "no bin/fstar.exe in $SRC/fstar.tar.gz"
(cd "$top" && tar -cf - .) | tar -xf - -C "$DEST"
printf 'repo: %s\nref: %s\ncommit: %s\n' "$REPO" "$REF" "$COMMIT" > "$DEST/SOURCE"
"$DEST/bin/fstar.exe" --version
