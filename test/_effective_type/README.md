# Effective types (C11 6.5p6/p7)

`effective_type.c` is a corpus of 61 cases covering the effective-type rules,
each tagged `[DEFINED]`, `[UB]`, `[UNSPEC]` or `[IMPL-DEF]` and cited to
N1570. It is a standalone C program -- it uses `<stdio.h>`, `printf` and
`malloc`, includes no `pal.h`, and carries no verification annotations -- so it
is a *specification to work against*, not a PAL test. Hence the `_` prefix,
which keeps it out of the test glob in `test/Makefile` and out of
`check-template.sh`, the same way `_templates` is kept out.

Sections 1-11 are defined, unspecified or implementation-defined behaviour and
should eventually be *accepted*. Sections 12-18 are undefined behaviour and
should eventually be *rejected* -- rejected for the right reason, which is the
hard part: most of them already fail to translate today, but because of the
ownership and alias analysis rather than because of 6.5p7. A test that passes
for an incidental reason locks the incidental reason in, so these should not
become `should-fail` tests until the rejection actually comes from the
effective-type rule.

Four tests do state the rule directly, by writing the ghost step a typed
access will become and putting the obligation on layer 0's `mem_pts_to_at`:
`test/etype_access_ok` (positive) and `test/etype_pun_bad`,
`test/etype_store_bad`, `test/etype_memcpy_bad` (negative, each pinned on the
rule it tests). See "Testing a rule that is not enforced yet" in `palow.md`
for why the positive one is not optional, and for the two ways a test here can
look like it passes while testing nothing.

Sections 19-22 -- `volatile`, `_Atomic`, `restrict`, object lifetime, and
modifying a `const` object or a string literal -- are not 6.5p6/p7 and belong
with the features they name rather than here.

Nineteen representative cases are transcribed as theorems in
`pulse/Pulse.Lib.C.Palow.Etype.fst`, named `case_<section>_<n>_<description>`
after the case they come from, so that the rules can be checked against the
standard before any of them is enforced on generated code: 1.2, 2.1, 3.3, 4.1,
5.1 and 6.1 as positive theorems, and 12.1-12.4, 13.1-13.3, 14.1-14.3, 15.4 and
17.1-17.2 as negative ones. Transcribing them is what turned up the three gaps
in the model that `palow.md` now records.

Two of the section-17 cases are stated as *positive* theorems, because the
model accepts what C calls undefined; both carry a comment saying why, so that
neither can be mistaken for enforcement. See the "Effective types" section of
`palow.md` for what enforcement still needs.
