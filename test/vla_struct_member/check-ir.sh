#!/bin/sh
set -eu

here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
pal=${C2PULSE:-"$here/../../target/debug/pal"}
clang=${CLANG:-clang}
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT HUP INT TERM

ast=$($clang -DC2PULSE -I"$here" -Xclang -ast-dump -fsyntax-only \
    "$here/vla_struct_member.c")
record=$(printf '%s\n' "$ast" \
    | sed -n '/RecordDecl.* explicitly_refined_member definition/,/FunctionDecl/p')
printf '%s\n' "$record" | grep -A1 "FieldDecl.* member 'int\[\]'" \
    | grep -F 'AnnotateAttr' | grep -Fq '"pal-refine"'

ir=$($pal --print-ir "$here/vla_struct_member.c")
$pal --outdir "$tmp" "$here/vla_struct_member.c"

count=$(printf '%s\n' "$ir" | grep -Fc 'int32_t[]')
test "$count" -eq 3
! printf '%s\n' "$ir" | grep -Fq 'int32_t[0] member;'
# The refinement is printed on the member itself in IR. This position is fed
# exclusively by the Clang FieldDecl attribute path, not record/typedef attrs.
field=$(printf '%s\n' "$ir" | sed -n '/struct explicitly_refined_member {/,/};/p' \
    | tr '\n' ' ' | sed 's/[[:space:]][[:space:]]*/ /g')
printf '%s\n' "$field" | grep -Fq \
    '_refine((_slprop) (this.member._length == (_specint) this.len)) int32_t[] member;'
! printf '%s\n' "$ir" | grep -Fq 'typedef struct explicitly_refined_member'

# Neither unrefined VLA spelling acquires a static length proposition in F*.
! grep -Fq 'length_of' "$tmp/Struct_incomplete_member.fst"
! grep -Fq 'length_of' "$tmp/Struct_zero_length_member.fst"

# The field-level relationship is part of the generated struct predicate.
# Scope the assertion to the predicate definition, not its fold/unfold helpers.
predicate=$(sed -n \
    '/let predicate struct_explicitly_refined_member__pred/,/let predicate struct_explicitly_refined_member__uninit_pred/p' \
    "$tmp/Struct_explicitly_refined_member.fst" \
    | tr '\n' ' ' | sed 's/[[:space:]][[:space:]]*/ /g')
printf '%s\n' "$predicate" | grep -Fq \
    '(length_of this.struct_explicitly_refined_member__member)) = (SizeT.v this.struct_explicitly_refined_member__len))'
