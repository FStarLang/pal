#!/usr/bin/env bash
# Check that the Palow specification surface (`pal --palow`, milestone 2 stage
# 1) typechecks for every test in the suite.
#
# This is deliberately not part of the per-test Makefiles: those are symlinks to
# a shared template, so they cannot carry per-test flags, and the Palow output
# is a single module per translation unit rather than one per declaration.
#
# The point of the check is narrow but load-bearing: the generated `fn`
# declarations mention the Palow points-to predicates, so F* accepting them is
# evidence that the translator's C-type-to-Palow-type mapping agrees with the
# model. Bodies are not emitted yet.
set -uo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.." || exit 1
ROOT=$PWD
PAL=${PAL:-$ROOT/target/debug/pal}
WORK=${WORK:-$ROOT/test/_palow}

rm -rf "$WORK"
mkdir -p "$WORK"

check_one() {
  local cfile=$1
  # One output directory per .c file, not per test directory: several tests
  # have more than one translation unit and they all produce a module of the
  # same name.
  local name
  name=$(basename "$(dirname "$cfile")")/$(basename "$cfile" .c)
  local dir="$WORK/$name"
  mkdir -p "$dir"

  local inc=()
  if [[ -d $(dirname "$cfile")/include ]]; then
    inc=(-I "$(dirname "$cfile")/include")
  fi

  if ! "$PAL" --quiet "${inc[@]}" --palow --outdir "$dir" "$cfile" 2>"$dir/pal.err"; then
    echo "FAIL $name (translation)"
    cat "$dir/pal.err"
    return 1
  fi

  local out
  if ! out=$(OTHERFLAGS="" "$ROOT/opt/run-fstar.sh" \
      --cache_checked_modules --cache_dir "$dir/_cache" \
      --already_cached 'Prims,FStar,Pulse.Nolib,Pulse.Class,Pulse.Lib,PulseCore' \
      --include "$ROOT/pulse/_cache" --include "$dir" \
      "$dir/PalowSpecs.fst" 2>&1); then
    echo "FAIL $name"
    echo "$out"
    return 1
  fi
  return 0
}

export -f check_one
export ROOT PAL WORK

if ! find test -mindepth 2 -maxdepth 2 -name '*.c' -print0 |
     xargs -0 -P "$(nproc)" -I{} bash -c 'check_one "$@"' _ {} |
     tee "$WORK/log"; then
  :
fi

if grep -q '^FAIL' "$WORK/log"; then
  echo "palow-check: failures above" >&2
  exit 1
fi

# The generated per-struct storage operations are model code, not translated
# C, so they do not count towards coverage.
emitted=$(cat "$WORK"/*/*/PalowSpecs.fst | grep '^fn ' | grep -cvE '^fn (struct|union)_')
skipped=$(cat "$WORK"/*/*/PalowSpecs.fst | grep -c '^(\* skipped')
admitted=$(cat "$WORK"/*/*/PalowSpecs.fst | grep -c 'admit() (\* body')
echo "palow-check: ok; $emitted specifications, $((emitted - admitted)) with bodies, $admitted admitted, $skipped skipped"
