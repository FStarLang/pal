#!/bin/bash
set -e

if [ -z "$1" ]; then
  echo "Usage: $0 <test_name>"
  echo "Creates a new test directory with the required symlinks."
  exit 1
fi

DIR="$(cd "$(dirname "$0")" && pwd)"
NAME="$1"

if [ -d "$DIR/$NAME" ]; then
  echo "Error: test/$NAME already exists" >&2
  exit 1
fi

mkdir -p "$DIR/$NAME"
ln -s ../_templates/Makefile "$DIR/$NAME/Makefile"
ln -s ../_templates/fstar.fst.config.json "$DIR/$NAME/fstar.fst.config.json"
ln -s ../_templates/pal.config.json "$DIR/$NAME/pal.config.json"
ln -s ../pal.h "$DIR/$NAME/pal.h"

cat > "$DIR/$NAME/$NAME.c" << 'EOF'
#include "pal.h"
#include <stdint.h>

EOF

echo "Created test/$NAME/ — edit test/$NAME/$NAME.c"
