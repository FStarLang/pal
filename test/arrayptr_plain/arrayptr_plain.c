// Test: an arrayptr flowing into a parameter that wants no ownership.
//
// PAL models `ref t` and `array t` as the SAME underlying handle, so
// `array_to_ref` is the identity coercion: it reads nothing and carries no
// ownership. That makes it exactly the right bridge when an interior pointer
// (`tab + off`, an arrayptr) is handed to a parameter declared `_plain` -- the
// idiom for a libc string input, which is read but not owned.
//
// Before this coercion existed PAL emitted the arrayptr unchanged and F*
// rejected the call with "Expected expression of type ref Int8.t, got ...
// array Int8.t" -- a type error in the generated code rather than a proof
// obligation the user could act on.
//
// Contrast with test/arrayptr_ref, which is the OTHER direction: a parameter
// that does want ownership, reached through a named plain-pointer local, which
// lowers to the executable `arrayptr_borrow_cell` and carves a cell out of the
// parent array. That path is unchanged; this one is for parameters that ask
// for nothing.
//
// This is MsQuic-shaped and coco-shaped alike: `strcmp(strtab + name_off, want)`
// while walking an ELF string table.
//
// FALSIFICATION, run by hand (the harness has no expected-failure mechanism).
// The claim worth testing is that the coercion does not INVENT ownership.
// Adding
//
//     void observe(const char *p);            // no _plain: wants it owned
//     int look_owned(_array const char *tab, size_t off)
//       _requires(off < tab._length)
//     { observe(tab + off); return 0; }
//
// must NOT verify, and does not: "Error 228 ... Cannot prove:
// Pulse.Lib.Reference.pts_to (array_to_ref __anf2) _". If the coercion ever
// started handing out a borrow, that would go green. Note the shape of the
// failure -- an unproved `pts_to`, i.e. a proof obligation -- which is the
// whole improvement over the ill-typed term it used to be.

#include "pal.h"
#include <stddef.h>
#include <stdint.h>

int cmp(_plain const char *a, _plain const char *b);

// (1) The interior pointer `tab + off`, straight into a `_plain` parameter.
// `off < tab._length` is not needed for the call itself -- `_plain` asks for
// nothing -- but it is what makes the C meaningful, and it must not make the
// obligation go away, so it is stated.
int look(_array const char *tab, size_t off, _plain const char *want)
  _requires(off < tab._length)
{
    return cmp(tab + off, want);
}

// (2) The same coercion from an `_arrayptr`-typed local rather than from an
// `_array` plus arithmetic.
int look_named(_array const char *tab, size_t off, _plain const char *want)
  _requires(off < tab._length)
{
    _arrayptr const char *p = tab + off;
    int r = cmp(p, want);
    _ghost_stmt(arrayptr_drop $(p));
    return r;
}

// (3) The array itself (offset zero), not an interior pointer.
int look_base(_array const char *tab, _plain const char *want)
{
    return cmp(tab, want);
}
