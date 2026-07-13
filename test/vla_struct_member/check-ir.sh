#!/bin/sh
set -eu

here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
pal=${C2PULSE:-"$here/../../target/debug/pal"}
ir=$($pal --print-ir "$here/vla_struct_member.c")

count=$(printf '%s\n' "$ir" | grep -Fc 'int32_t[] member;')
test "$count" -eq 3
! printf '%s\n' "$ir" | grep -Fq 'int32_t[0] member;'
printf '%s\n' "$ir" \
    | grep -Fq '_refine((_slprop) (this._length == 2)) int32_t[] member;'
