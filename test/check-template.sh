#!/bin/bash
# Verify that every test directory matches the template laid out by test/new.sh:
# four symlinks (Makefile, fstar.fst.config.json, pal.config.json, pal.h) with
# the expected targets, and at least one .c file.
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
  for f in "${!EXPECTED[@]}"; do
    expected="${EXPECTED[$f]}"
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
done < <(find "$DIR" -mindepth 1 -maxdepth 1 -type d \
            ! -name '_*' ! -name '.*' | sort)

exit "$status"
