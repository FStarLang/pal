#!/usr/bin/env bash
#
# Build `pal` inside a checkout of the repository, run the translation step of
# the test suite, and copy the generated F* files into a snapshot directory.
#
# The snapshot directories produced by two different checkouts can then be
# diffed against each other to see how a change affects the generated code.
#
# Usage: pal-snapshot.sh <worktree> <snapshot-dir>

set -euo pipefail

if [ $# -ne 2 ]; then
  echo "usage: $0 <worktree> <snapshot-dir>" >&2
  exit 2
fi

worktree=$(cd "$1" && pwd)
mkdir -p "$2"
snapshot=$(cd "$2" && pwd)

cd "$worktree"

# CI shares one CARGO_TARGET_DIR between the base and head checkouts so that
# dependencies are compiled only once. Cargo decides freshness from file
# modification times, and a freshly created worktree can look older than the
# artifacts left behind by the previous snapshot, which would silently reuse
# the wrong `pal` binary. Touching the tracked sources forces a rebuild of the
# crate itself while leaving the dependency artifacts intact.
if git rev-parse --is-inside-work-tree >/dev/null 2>&1; then
  git ls-files -z | xargs -0 touch
fi

echo "::group::Building pal in $worktree"
cargo build
echo "::endgroup::"

if [ -n "${CARGO_TARGET_DIR:-}" ]; then
  pal_bin="$CARGO_TARGET_DIR/debug/pal"
else
  pal_bin="$worktree/target/debug/pal"
fi

if [ ! -x "$pal_bin" ]; then
  echo "error: pal binary not found at $pal_bin" >&2
  exit 1
fi

echo "::group::Translating tests in $worktree"
# Invoke `pal` directly rather than going through the test Makefiles: this
# script has to work unchanged against older commits of the repository, whose
# build rules may differ.
#
# Translation failures must not abort the snapshot: a diff that shows tests
# going from "translated" to "failed to translate" is exactly the kind of
# regression this report is meant to surface.
find test -mindepth 1 -maxdepth 1 -type d \
  ! -name '_*' ! -name '.*' -print0 |
  PAL_BIN="$pal_bin" xargs -0 -P "$(nproc)" -I{} bash -c '
    set -u
    dir="$1"
    cd "$dir" || exit 0
    opts=()
    [ -d include ] && opts+=(-I include)
    "$PAL_BIN" "${opts[@]}" --outdir out *.c >/dev/null 2>&1 ||
      echo "warning: pal failed in $dir" >&2
  ' _ {}
echo "::endgroup::"

# Collect the generated F* sources and diagnostics. `source_range_info.json` is
# deliberately skipped: it is machine-oriented data that changes with every
# formatting tweak and would drown out the interesting parts of the diff.
for dir in test/*/; do
  name=$(basename "$dir")
  outdir="$dir/out"
  [ -d "$outdir" ] || continue

  found=0
  for file in "$outdir"/*.fst "$outdir"/*.fsti "$outdir"/diagnostics.json; do
    [ -f "$file" ] || continue
    if [ "$found" -eq 0 ]; then
      mkdir -p "$snapshot/$name"
      found=1
    fi
    # Absolute paths leak into diagnostics.json; strip the checkout prefix so
    # that the base and head snapshots stay comparable.
    sed "s|$worktree/||g" "$file" >"$snapshot/$name/$(basename "$file")"
  done
done

echo "Snapshot written to $snapshot ($(find "$snapshot" -type f | wc -l) files)"
