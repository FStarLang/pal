#!/bin/bash
# Verify that every test directory matches the template laid out by test/new.sh:
# four symlinks (Makefile, fstar.fst.config.json, pal.config.json, pal.h) with
# the expected targets, and at least one .c file. A diagnostic test (test/new.sh
# -d) instead symlinks Makefile to ../_templates/Makefile.diagnostic and lists
# what PAL must report in expected-diagnostics.txt.
set -u

DIR="$(cd "$(dirname "$0")" && pwd)"

declare -A EXPECTED=(
  [Makefile]="../_templates/Makefile"
  [fstar.fst.config.json]="../_templates/fstar.fst.config.json"
  [pal.config.json]="../_templates/pal.config.json"
  [pal.h]="../pal.h"
)

status=0

while IFS= read -r d; do
  name="$(basename "$d")"
  diagnostic=0
  if [ "$(readlink "$d/Makefile" 2>/dev/null)" = "../_templates/Makefile.diagnostic" ]; then
    diagnostic=1
  fi
  for f in "${!EXPECTED[@]}"; do
    expected="${EXPECTED[$f]}"
    if [ "$f" = Makefile ] && [ "$diagnostic" = 1 ]; then
      expected="../_templates/Makefile.diagnostic"
    fi
    path="$d/$f"
    if [ ! -L "$path" ]; then
      echo "ERROR: test/$name/$f is missing or not a symlink (expected symlink to $expected; see test/new.sh)" >&2
      status=1
      continue
    fi
    actual="$(readlink "$path")"
    if [ "$actual" != "$expected" ]; then
      echo "ERROR: test/$name/$f symlinks to '$actual', expected '$expected' (see test/new.sh)" >&2
      status=1
    fi
  done
  if ! compgen -G "$d/*.c" >/dev/null; then
    echo "ERROR: test/$name has no .c file (see test/new.sh)" >&2
    status=1
  fi
  if [ "$diagnostic" = 1 ] && [ ! -f "$d/expected-diagnostics.txt" ]; then
    echo "ERROR: test/$name is a diagnostic test but has no expected-diagnostics.txt (see test/new.sh)" >&2
    status=1
  fi
done < <(find "$DIR" -mindepth 1 -maxdepth 1 -type d \
            ! -name '_*' ! -name '.*' | sort)

exit "$status"
