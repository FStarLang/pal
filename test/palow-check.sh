#!/usr/bin/env bash
# Measure Palow's coverage of the test suite and typecheck the result.
#
# The per-test Makefiles already translate and verify against Palow -- it is
# the default model -- so what this adds is the census: it runs
# `--palow-permissive`, which puts an untranslated construct back into the
# generated file as a comment instead of reporting it as an error, and counts
# the comments. With no gaps left the two agree, and the number is what says
# so.
set -uo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.." || exit 1
ROOT=$PWD
PAL=${PAL:-$ROOT/target/debug/pal}
WORK=${WORK:-$ROOT/test/_palow}

rm -rf "$WORK"
mkdir -p "$WORK"

check_one() {
  local tdir=$1
  # One output directory per *test*, translated in a single invocation with all
  # of the test's files, which is how the per-test Makefile drives PAL. A file
  # is not a translation unit here: PAL combines them, and several tests rely on
  # that -- `extern_globals` states a contract about a `const` whose value is
  # written down in a sibling file, and reading them apart would say only that
  # the value is fixed, not which one it is.
  local name
  name=$(basename "$tdir")
  local dir="$WORK/$name"
  mkdir -p "$dir"

  local inc=()
  if [[ -d $tdir/include ]]; then
    inc=(-I "$tdir/include")
  fi

  local cfiles=("$tdir"/*.c)
  if ! "$PAL" --quiet "${inc[@]}" --palow-permissive --outdir "$dir" "${cfiles[@]}" 2>"$dir/pal.err"; then
    echo "FAIL $name (translation)"
    cat "$dir/pal.err"
    return 1
  fi

  # One module per declaration means the dependency order between the
  # generated files is no longer the order they were written in, so F* has to
  # be asked for it. `verify.mk` already does exactly that for the old
  # translator's output, and it is generic over the directory.
  # A test may ship hand-written F* beside its C. `verify.mk` looks for that
  # directory relative to the working directory, and this runs from the repo
  # root rather than from the test, so the include is passed explicitly.
  #
  # `helpers_palow` takes precedence when it exists. A helper module is written
  # against the memory model, so a test whose helpers mention the old model's
  # predicates needs a second copy -- but the *C* should not have to know which
  # one it is getting, so the two copies use the same module name and the
  # include path chooses. Annotation churn in the C is the thing being
  # measured; moving it into the include path keeps the measurement honest.
  local helpers=""
  if [[ -d $tdir/helpers_palow ]]; then
    helpers=" --include $tdir/helpers_palow"
  elif [[ -d $tdir/helpers ]]; then
    helpers=" --include $tdir/helpers"
  fi

  local out
  if ! out=$(OTHERFLAGS="" make -s -f "$ROOT/test/verify.mk" \
      OUT_DIR="$dir" CACHE_DIR="$dir/_cache" DEPEND="$dir/.depend" \
      FSTAR_EXE="$ROOT/opt/run-fstar.sh --include $ROOT/pulse/_cache$helpers" 2>&1); then
    echo "FAIL $name"
    echo "$out"
    return 1
  fi
  return 0
}

export -f check_one
export ROOT PAL WORK

if ! find test -mindepth 1 -maxdepth 1 -type d -exec test -n '{}' \; -print0 |
     xargs -0 -P "$(nproc)" -I{} bash -c 'ls "$1"/*.c >/dev/null 2>&1 && check_one "$1"' _ {} |
     tee "$WORK/log"; then
  :
fi

if grep -q '^FAIL' "$WORK/log"; then
  echo "palow-check: failures above" >&2
  exit 1
fi

# The generated per-struct storage operations, the per-shape array fill and
# read recursions, and the `__fp` wrappers are model code, not translated C,
# so they do not count towards coverage.
emitted=$(cat "$WORK"/*/*.fst | grep '^fn ' | grep -cvE '^fn (rec )?(struct|union|array)_|__fp ')
skipped=$(cat "$WORK"/*/*.fst | grep -c '^(\* skipped')
admitted=$(cat "$WORK"/*/*.fst | grep -c 'admit() (\* body')
# A function declared here and defined elsewhere has no body to translate, so
# it is neither covered nor a gap. Counting it as an admit would make the
# measurement say the translation failed at something it was never given.
external=$(cat "$WORK"/*/*.fst | grep -c '(\* external:')
echo "palow-check: ok; $emitted specifications, $((emitted - admitted - external)) with bodies, $admitted admitted, $external external, $skipped skipped"
