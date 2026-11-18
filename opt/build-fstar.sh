#!/usr/bin/env bash
#
# Build an F* binary distribution from F* sources, the way F*'s nightly builds
# do (make package ADMIT=1), and install it into DIR: DIR/bin/fstar.exe and
# DIR/lib/fstar/{ulib,ulib.checked,pulse,z3-*,...}, the layout that
# opt/install-fstar.sh --dest DIR produces and that opt/package.sh --fstar DIR
# bundles. The sources are one of:
# - a git ref of an F* repository (--ref), or a git checkout (--src DIR): a
#   full (bootstrapping) build, on Linux and macOS only;
# - an F* source package (fstar-src.tar.gz, as made by --make-src-package or
#   F*'s `make package-src`), unpacked (--src DIR) or not (--src-package
#   FILE): it builds on Linux, macOS and Windows (in a Cygwin shell with OCaml
#   from opam, as F*'s Windows builds do).
#
# Usage: opt/build-fstar.sh [--dest DIR] [--make-src-package OUTDIR]
#                           (--ref REF [--repo URL] | --src DIR | --src-package FILE)
#                           [--work DIR] [--jobs N] [--install-deps]
#        opt/build-fstar.sh --print-commit --ref REF [--repo URL]
#   --dest DIR      install the F* binary distribution into DIR
#   --make-src-package OUTDIR  make OUTDIR/fstar-src.tar.gz, an F* source
#                   package, and OUTDIR/fstar-src.SOURCE (from git sources)
#   --ref REF       branch, tag or full commit SHA of --repo
#   --repo URL      default: https://github.com/FStarLang/FStar.git
#   --src DIR       an F* git checkout (with its submodules; built in place)
#                   or an unpacked F* source package
#   --src-package FILE  an F* source package (.tar.gz); FILE's repository and
#                   ref are read from FILE with .tar.gz replaced by .SOURCE
#   --work DIR      where to clone --repo or unpack --src-package (default: a
#                   temporary directory)
#   --install-deps  first install F*'s OCaml dependencies with opam
#   --print-commit  only print the commit SHA that REF denotes in --repo
# Requirements: OCaml (>= 4.14; F*'s builds use 5.3.0) with F*'s opam
#   dependencies (or --install-deps), GNU make (gmake on macOS), curl, unzip,
#   gmp (e.g. on macOS: brew install opam make gmp), git for git sources.
# Environment: FSTAR_VERSION (the version that fstar.exe --version prints,
#   default for git sources: git-<12-digit commit>; source packages keep
#   theirs).
# Writes DIR/SOURCE: the repository, ref, commit and kind of sources that F*
# was built from (for a modified checkout: commit-dirty, and the sha256 of
# its git diff).

set -euo pipefail

usage() { sed -n '3,40p' "$0" | sed 's/^# \{0,1\}//'; exit "${1:-0}"; }
die() { echo "build-fstar.sh: $*" >&2; exit 1; }

REPO=https://github.com/FStarLang/FStar.git
REF=""
SRC=""
SRC_PACKAGE=""
DEST=""
SRC_OUT=""
WORK=""
JOBS="$(nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 2)"
INSTALL_DEPS=0
PRINT_COMMIT=0
while [[ $# -gt 0 ]]; do
    case "$1" in
        --ref) REF="$2"; shift 2 ;;
        --repo) REPO="$2"; shift 2 ;;
        --src) SRC="$2"; shift 2 ;;
        --src-package) SRC_PACKAGE="$2"; shift 2 ;;
        --dest) DEST="$2"; shift 2 ;;
        --make-src-package) SRC_OUT="$2"; shift 2 ;;
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

[[ -n "$DEST" || -n "$SRC_OUT" ]] || die "--dest or --make-src-package is required"
n=0
for s in "$REF" "$SRC" "$SRC_PACKAGE"; do [[ -z "$s" ]] || n=$((n + 1)); done
[[ $n == 1 ]] || die "give exactly one of --ref, --src and --src-package"
[[ -z "$SRC_OUT" || -z "$SRC_PACKAGE" ]] ||
    die "--make-src-package needs git sources (--ref, or --src with a git checkout)"

WINDOWS=0
case "$(uname -s)" in
    Linux) MAKE="make" ;;
    Darwin) MAKE="gmake" ;;
    CYGWIN*|MINGW*|MSYS*) MAKE="make"; WINDOWS=1 ;;
    *) die "unsupported OS: $(uname -s)" ;;
esac
command -v "$MAKE" >/dev/null || die "missing tool: $MAKE (GNU make)"
for tool in curl unzip; do
    command -v "$tool" >/dev/null || die "missing tool: $tool"
done
[[ -z "$REF" ]] || command -v git >/dev/null || die "missing tool: git"

sha256() { if command -v sha256sum >/dev/null; then sha256sum; else shasum -a 256; fi | cut -d' ' -f1; }

if [[ -n "$DEST" ]]; then
    mkdir -p "$DEST"
    DEST="$(cd "$DEST" && pwd)"
    # DEST is emptied before installing: only if it is empty or an F* install.
    [[ -z "$(ls -A "$DEST")" || -f "$DEST/bin/fstar.exe" ]] ||
        die "$DEST is neither empty nor an F* installation"
fi

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
WORK="${WORK:-$TMP}"
mkdir -p "$WORK"

# A source package's Makefile ends with lines that src-install.sh appends.
is_src_package() { grep -qs 'LINES BELOW ADDED BY src-install.sh' "$1/Makefile"; }

DIFF_SHA=""
if [[ -n "$REF" ]]; then
    COMMIT="$(resolve_commit)"
    KIND=git
    SRC="$WORK/FStar"
    echo "== fetching F* $REF ($COMMIT) from $REPO"
    rm -rf "$SRC"
    git init -q "$SRC"
    git -C "$SRC" remote add origin "$REPO"
    git -C "$SRC" fetch -q --depth 1 origin "$COMMIT"
    git -C "$SRC" checkout -q --detach FETCH_HEAD
elif [[ -n "$SRC_PACKAGE" ]]; then
    [[ -f "$SRC_PACKAGE" ]] || die "no such file: $SRC_PACKAGE"
    info="${SRC_PACKAGE%.tar.gz}.SOURCE"
    if [[ -f "$info" ]]; then
        REPO="$(sed -n 's/^repo: //p' "$info")"
        REF="$(sed -n 's/^ref: //p' "$info")"
    else
        REPO="$(cd "$(dirname "$SRC_PACKAGE")" && pwd)/$(basename "$SRC_PACKAGE")"
        REF="source package"
    fi
    echo "== unpacking $SRC_PACKAGE"
    rm -rf "$WORK/fstar-src"
    mkdir -p "$WORK/fstar-src"
    tar -xzf "$SRC_PACKAGE" -C "$WORK/fstar-src"
    SRC="$(dirname "$(find "$WORK/fstar-src" -maxdepth 3 -name fstar.opam | head -1)")"
    [[ "$SRC" != . ]] || die "$SRC_PACKAGE is not an F* source package"
else
    SRC="$(cd "$SRC" && pwd)" || die "no such directory: $SRC"
fi

if [[ -n "$SRC_PACKAGE" ]] || { [[ -z "$REF" ]] && is_src_package "$SRC"; }; then
    is_src_package "$SRC" || die "$SRC is not an F* source package"
    KIND=src-package
    if [[ -z "$SRC_PACKAGE" ]]; then REPO="$SRC"; REF="source package"; fi
    COMMIT="$(sed -n 's/^export FSTAR_COMMIT=//p' "$SRC/Makefile" | tail -1)"
elif [[ -z "$REF" ]]; then
    [[ -e "$SRC/.git" ]] || die "$SRC is neither an F* git checkout nor an F* source package"
    KIND=git
    REPO="$(git -C "$SRC" remote get-url origin 2>/dev/null || echo "$SRC")"
    REF="$(git -C "$SRC" describe --all --always 2>/dev/null || echo unknown)"
    COMMIT="$(git -C "$SRC" rev-parse HEAD)"
    if [[ -n "$(git -C "$SRC" status --porcelain --untracked-files=no)" ]]; then
        COMMIT="$COMMIT-dirty"
        DIFF_SHA="$(git -C "$SRC" diff HEAD | sha256)"
    fi
fi
[[ -f "$SRC/fstar.opam" ]] || die "$SRC is not an F* source tree"
if [[ $KIND == git ]]; then
    [[ $WINDOWS == 0 ]] ||
        die "F* does not build from git sources on Windows: make a source package on Linux (--make-src-package)"
    git -C "$SRC" submodule update -q --init --recursive
    export FSTAR_VERSION="${FSTAR_VERSION:-git-${COMMIT:0:12}}"
elif [[ -n "$SRC_OUT" ]]; then
    die "--make-src-package needs git sources (--ref, or --src with a git checkout)"
fi

# The OCaml switch that opam would select (no-op if already in the environment).
if command -v opam >/dev/null; then eval "$(opam env 2>/dev/null)" || true; fi
if [[ $INSTALL_DEPS == 1 ]]; then
    echo "== installing F*'s OCaml dependencies"
    opam_file="$SRC/fstar.opam"
    # opam on Windows is a native program: it does not understand Cygwin paths.
    [[ $WINDOWS == 0 ]] || opam_file="$(cygpath -m "$opam_file")"
    opam install -y --deps-only "$opam_file"
    eval "$(opam env)"
fi
command -v ocamlfind >/dev/null || command -v dune >/dev/null ||
    die "OCaml and F*'s dependencies not found (opam install --deps-only fstar.opam, or --install-deps)"

# A .tar.gz on every OS (F* makes a .zip on Windows by default).
export FSTAR_PACKAGE_FORMAT=tar.gz
rm -f "$SRC/fstar.tar.gz" "$SRC/fstar-src.tar.gz"
if [[ -n "$SRC_OUT" ]]; then
    echo "== making the F* source package (make package-src ADMIT=1)"
    "$MAKE" -C "$SRC" -skj"$JOBS" package-src ADMIT=1 FSTAR_TAG=
    mkdir -p "$SRC_OUT"
    cp "$SRC/fstar-src.tar.gz" "$SRC_OUT/"
    printf 'repo: %s\nref: %s\ncommit: %s\n' "$REPO" "$REF" "$COMMIT" > "$SRC_OUT/fstar-src.SOURCE"
    echo "== wrote $SRC_OUT/fstar-src.tar.gz"
fi
[[ -n "$DEST" ]] || exit 0

# make package bundles z3 with F*'s .scripts/package_z3.sh, which ignores a
# failing download (then the package just lacks z3): try F*'s download script
# first, to fail early and show why.
echo "== checking that F*'s z3 versions can be downloaded"
if ! "$SRC/.scripts/get_fstar_z3.sh" --full "$TMP/z3" >/dev/null; then
    echo "== get_fstar_z3.sh failed; tracing it (curl and unzip: $(type -ap curl unzip | paste -sd' ' -))" >&2
    rm -rf "$TMP/z3"
    bash -x "$SRC/.scripts/get_fstar_z3.sh" --full "$TMP/z3" >&2 || true
    die "cannot download z3 with F*'s .scripts/get_fstar_z3.sh"
fi
rm -rf "$TMP/z3"

if [[ $KIND == git ]]; then
    echo "== building F* (make package ADMIT=1)"
    "$MAKE" -C "$SRC" -skj"$JOBS" package ADMIT=1 FSTAR_TAG=
else
    echo "== building F* from the source package (make ADMIT=1; make package)"
    "$MAKE" -C "$SRC" -skj"$JOBS" ADMIT=1
    if [[ $WINDOWS == 1 ]]; then
        # The libgmp DLL that fstar.exe loads, to ship next to it (which
        # libgmp-10.dll may find a 32-bit one).
        ldd_out="$(ldd "$SRC/out/bin/fstar.exe")"
        LIBGMP="$(sed -n 's/^[[:space:]]*libgmp-10.dll => *\([^ ]*\) .*$/\1/p' <<<"$ldd_out")"
        # ldd may not list it: then the 64-bit MinGW one on the PATH (fstar.exe
        # is a 64-bit MinGW program).
        [[ -n "$LIBGMP" ]] || LIBGMP="$(type -ap libgmp-10.dll | grep -m1 x86_64-w64-mingw32 || true)"
        if [[ ! -f "$LIBGMP" ]]; then
            echo "$ldd_out" >&2
            die "cannot find the libgmp-10.dll that fstar.exe loads"
        fi
        echo "== shipping $LIBGMP"
        export LIBGMP
    fi
    "$MAKE" -C "$SRC" -s package ADMIT=1 FSTAR_TAG=
fi

echo "== installing into $DEST"
find "$DEST" -mindepth 1 -delete
mkdir "$TMP/pkg"
tar -xzf "$SRC/fstar.tar.gz" -C "$TMP/pkg"
# The archive's top directory (fstar/ or ./fstar/).
top="$(dirname "$(dirname "$(find "$TMP/pkg" -path '*/bin/fstar.exe' | head -1)")")"
[[ "$top" != . ]] || die "no bin/fstar.exe in $SRC/fstar.tar.gz"
(cd "$top" && tar -cf - .) | tar -xf - -C "$DEST"
compgen -G "$DEST/lib/fstar/z3-*/bin/z3*" >/dev/null ||
    die "no z3 in $SRC/fstar.tar.gz (see make package's output)"
{
    printf 'repo: %s\nref: %s\ncommit: %s\nkind: %s\n' "$REPO" "$REF" "$COMMIT" "$KIND"
    [[ -z "$DIFF_SHA" ]] || printf 'diff_sha256: %s\n' "$DIFF_SHA"
} > "$DEST/SOURCE"
"$DEST/bin/fstar.exe" --version
