#include "pal.h"
#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>

// ===========================================================================
// arrayptr <-> ref: the four ways a pointer of "array" kind meets one of "ref"
// kind, and how PAL bridges them.
//
// PAL models a C pointer as one of three abstract Pulse types:
//   * `ref t`      -- a single-cell reference (from a plain `int*`);
//   * `array t`    -- an owning array (`_array`);
//   * `array t`    -- a non-owning *arrayptr* (`_arrayptr`; carries a pure,
//                     duplicable `arrayptr_pts_to` witness into a parent array).
// `ref t` and `array t` are DIFFERENT abstract types, so an arrayptr and a ref
// cannot be used interchangeably at the Pulse level without an explicit bridge.
// This test exercises every bridge PAL inserts.
// ===========================================================================

typedef struct {
    uint64_t Low;
    uint64_t Count;
} SUBRANGE;

// ---------------------------------------------------------------------------
// (1) Passing an arrayptr where a plain (write-only) `int*` is expected.
//
// An arrayptr owns nothing, so to hand its cell to a function taking an
// `_out int*` (a write-only `ref`) the pointed-at cell must first be *borrowed*
// from the still-live parent array. The borrow is spelled as a plain-pointer
// local initialized from the arrayptr (`int* c = p;`), which PAL lowers to the
// executable `arrayptr_borrow_cell` -- carving the cell out of the parent as a
// maybe-initialized `ref`. PAL emits no ghost steps of its own: handing `c` to
// the `_out` parameter drops it to a write-only `pts_to_uninit` through the
// `[@@pulse_intro]` `forget_maybe` automatically, and the user gives the cell
// back explicitly with the index-inferring `array_return_cell`, the
// `[@@pulse_intro]` `intro_maybe_some` repackaging the now-written cell on the
// way in.
// ---------------------------------------------------------------------------

void fill(_out int* out)
{
  *out = 42;
}

void pass_arrayptr_as_ref(_array int* a)
  _requires(a._length == 3)
{
  _arrayptr int* p = a + 1;
  int* c = p;
  fill(c);
  _ghost_stmt(array_return_cell $(a));
  _ghost_stmt(arrayptr_drop $(p));
}

// ---------------------------------------------------------------------------
// (2) A function *returning* an arrayptr that the caller consumes as a `ref`.
//
// This is the insert path of MsQuic's `QuicRangeAddRange`, faithfully split
// across a helper:
//
//     SUBRANGE* Sub = get_uninit(a);   // helper hands back &a[0]
//     Sub->Low   = ...;                // caller fills the hole field by field
//     Sub->Count = ...;
//
// `get_uninit` keeps the parent array live and exposes the arrayptr link plus
// its offset (so the borrow's index into the parent is pinned). The caller
// stores the returned arrayptr straight into a plain-pointer local `Sub`, which
// PAL models as a `ref` borrowed out of the parent: it emits
// `arrayptr_borrow_cell` on the (anonymous, inlined) returned arrayptr, handing
// back a maybe-initialized cell the user fills field by field. The cell is
// given back with the single `array_return_cell $(a)`, whose parent index is
// *inferred* from the carved-array resource -- so it works even though the
// borrowed cell sits at the arrayptr's symbolic offset rather than a literal
// index, and no named arrayptr handle needs to survive the borrow.
// ---------------------------------------------------------------------------

_arrayptr SUBRANGE* get_uninit(_plain _array SUBRANGE* a)
  _requires(_inline_pulse(array_pts_to_uninit $(a) $`v))
  _ensures(_inline_pulse(
    array_pts_to_uninit $(a) $`v **
    arrayptr_pts_to $(return) $(a) **
    pure (offset_of $(return) == offset_of $(a))))
{
    return &a[0];
}

void consume_returned_arrayptr_as_ref(_out _array SUBRANGE* a)
  _requires(a._length == 1)
{
    SUBRANGE* Sub = get_uninit(a);
    _ghost_stmt(Pulse.Lib.C.MaybeUninit.forget_maybe $(Sub));
    _ghost_stmt($unfold-uninit(SUBRANGE) $(Sub));
    Sub->Low = 10;
    Sub->Count = 5;
    _ghost_stmt($fold(SUBRANGE) $(Sub) _ _);
    _ghost_stmt(Pulse.Lib.C.MaybeUninit.intro_maybe_some $(Sub));
    _ghost_stmt(array_return_cell $(a));
}

// ---------------------------------------------------------------------------
// (3) An equality comparison between an arrayptr and a ref.
//
// The two abstract pointer types are not directly comparable, so PAL erases
// both operands to their raw base+offset machine address and compares those
// with `core_ref_eq` -- true iff they name the same location. The arrayptr
// shares the same underlying handle as a ref, so it is first converted to a
// ref (`array_to_ref`, the identity coercion) and then both operands go through
// the single `ref_to_core` primitive. The comparison reads nothing, so neither
// operand needs any ownership.
// ---------------------------------------------------------------------------

bool same_loc(_arrayptr int* p, _plain int* q)
{
  return p == q;
}

// ---------------------------------------------------------------------------
// (4) A plain-pointer local assigned `&a[i]` (borrow a cell to a local ref).
//
// The no-helper, in-place variant of (2): the cell address is taken directly
// (`SUBRANGE* Sub = &a[0];`) rather than obtained from a returned arrayptr, so
// PAL emits `array_borrow_cell` (not `arrayptr_borrow_cell`). It hands the cell
// back as a maybe-initialized cell we fill field by field and return with
// `array_return_cell`. A `Sub->field = v` on an *arrayptr* would instead
// lower to `arrayptr_update`, a whole-cell read-modify-write that REQUIRES the
// cell already initialized -- so it cannot fill an uninitialized hole.
// ---------------------------------------------------------------------------

void assign_cell_address_to_ref(_out _array SUBRANGE* a)
  _requires(a._length == 1)
{
    SUBRANGE* Sub = &a[0];
    _ghost_stmt(Pulse.Lib.C.MaybeUninit.forget_maybe $(Sub));
    _ghost_stmt($unfold-uninit(SUBRANGE) $(Sub));
    Sub->Low = 10;
    Sub->Count = 5;
    _ghost_stmt($fold(SUBRANGE) $(Sub) _ _);
    _ghost_stmt(Pulse.Lib.C.MaybeUninit.intro_maybe_some $(Sub));
    _ghost_stmt(array_return_cell $(a));
}
