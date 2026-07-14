#!/bin/sh
set -eu

here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
pal=${C2PULSE:-"$here/../../target/debug/pal"}
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT HUP INT TERM

ir=$($pal --print-ir "$here/vla_struct_member.c")
$pal --outdir "$tmp" "$here/vla_struct_member.c"

count=$(printf '%s\n' "$ir" | grep -Fc 'int32_t[] member;')
test "$count" -eq 3
! printf '%s\n' "$ir" | grep -Fq 'int32_t[0] member;'
printf '%s\n' "$ir" \
    | grep -Fq '_refine((_slprop) (this.member._length == (_specint) this.len))'

# Neither unrefined VLA spelling acquires a static length proposition in F*.
! grep -Fq 'length_of' "$tmp/Struct_incomplete_member.fst"
! grep -Fq 'length_of' "$tmp/Struct_zero_length_member.fst"

# The explicit length-to-field relationship survives in the generated F*.
refinement=$(tr '\n' ' ' < "$tmp/Typedef_explicitly_refined_member.fst" \
    | sed 's/[[:space:]][[:space:]]*/ /g')
printf '%s\n' "$refinement" | grep -Fq \
    '(length_of this.Struct_explicitly_refined_member.struct_explicitly_refined_member__member)) = (SizeT.v this.Struct_explicitly_refined_member.struct_explicitly_refined_member__len))'
