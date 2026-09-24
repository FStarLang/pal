#include "pal.h"
#include <stdlib.h>
#include <stdint.h>

// A struct whose last field is a flexible array member (VLA in a struct). The
// `_refines` clause states that the length of the flexible array is always
// equal to the `len` field. PAL models `data` as an inline `array_spec` with
// no length pin; the refinement adds the `array_spec_len == len` relation to
// the struct predicate.
struct vec {
    unsigned len;
    _refines(this._length == len) int data[];
};

// Read an element of the flexible array. The precondition `i < v->len`, together
// with the `_refines` length relation carried by the struct predicate, lets the
// array read verify that `i` is in bounds. Preserving `i < v->len` keeps that
// bound in scope so the `v->data[i]` element postcondition is well-typed.
int vec_get(struct vec *v, unsigned i)
    _preserves(i < v->len)
    _ensures(return == v->data[i])
{
    return v->data[i];
}

// Write an element of the flexible array. Preserving `i < v->len` again keeps
// the index bound in scope for the `v->data[i]` element postcondition.
void vec_set(struct vec *v, unsigned i, int x)
    _preserves(i < v->len)
    _ensures(v->data[i] == x)
{
    v->data[i] = x;
}

/* Palow's allocators may fail, so the honest return type says so: everything
   the contract promises about the object holds only when there is one. PAL's
   FAM allocators are infallible, so the nullable spelling -- and the test that
   goes with it -- is Palow's alone. */
#ifdef PALOW
_allocated _nullable typedef struct vec *vec_ptr;
#else
_allocated typedef struct vec *vec_ptr;
#endif

// Allocate and zero-initialize a vec using the idiomatic flexible-array-member
// calloc: `calloc(1, sizeof(struct vec) + n * sizeof(int))`. This is the
// zeroing counterpart of the FAM malloc idiom and mirrors MsQuic's
// `QuicCidNewNullSource`, which allocates the sized block and zeroes it. It
// translates to a sized FAM allocation (`struct_vec__aux_calloc_flex n`) that
// threads the tail length `n`: the returned struct is unfolded, with `len`
// uninitialized and the flexible `data` array zeroed with length `n`. Setting
// `v->len = n` initializes the length field and satisfies the `_refines` length
// relation (`array_spec_len data == len`), after which the struct auto-folds
// into a valid `struct vec` on return. Whole-struct assignment
// (`*v = (struct vec){ ... }`) is rejected for FAM structs since C does not copy
// the flexible array contents, so the struct must be constructed this way.
vec_ptr vec_new(unsigned n)
{
    struct vec *v = calloc(1, sizeof(struct vec) + n * sizeof(int));
#ifdef PALOW
    if (v == NULL) {
        return NULL;
    }
#endif
    v->len = n;
    return v;
}
// Allocate a vec using the idiomatic flexible-array-member malloc
// `malloc(sizeof(struct vec) + n * sizeof(int))` and fill it. This mirrors
// MsQuic's `QuicCidNewSource`, which mallocs the sized block and then populates
// the trailing array. It translates to a sized FAM allocation
// (`struct_vec__aux_malloc_flex n`) that threads the tail length `n`: the
// returned struct is unfolded, with `len` uninitialized and the flexible `data`
// array *uninitialized* with length `n`. Unlike the calloc idiom, the caller
// must fully initialize `data` before the struct can fold, so the fill loop
// carries an `_inline_pulse` frontier invariant stating the flexible array is
// initialized up to `i`. The invariant references PAL-internal names: the ghost
// array handle `Struct_vec.struct_vec__data_1 $(v)` and the unfolded-struct
// token `Struct_vec.struct_vec__aux_raw_unfolded $(v)` (both applied to the
// under-construction struct pointer `v`). Once `i == n` every element is
// initialized, so the tail is a full array and the struct auto-folds on return.
vec_ptr vec_new_filled(unsigned n, int x)
{
    struct vec *v = malloc(sizeof(struct vec) + n * sizeof(int));
#ifdef PALOW
    if (v == NULL) {
        return NULL;
    }
#endif
    v->len = n;
#ifdef PALOW
    /* Palow holds the unfilled tail as a sequence of `option`s at the address
       the field starts at, so the frontier invariant is about that sequence:
       it is as long as the allocation asked for, and everything below `i`
       holds a value. When the loop ends `i == n`, which is what lets the
       object be gathered. */
    for (unsigned i = 0; i < n; i = i + 1)
        _invariant(_live(i))
        _invariant(_inline_pulse(
            exists* (s: FStar.Seq.seq (option Int32.t)).
              (array_pts_to (maybe_repr int32_t_repr (SizeT.v 4sz)) (SizeT.v 4sz)
                 ($(v) +! Struct_vec.struct_vec_offsetof_data) 1.0R s) **
              (pure (FStar.Seq.length s == UInt32.v $(n))) **
              (pure (forall (k: nat). k < FStar.Seq.length s ==> k < UInt32.v $(i)
                                      ==> Some? (FStar.Seq.index s k)))
        ))
    {
        v->data[i] = x;
    }
#else
    for (unsigned i = 0; i < n; i = i + 1)
        _invariant(_live(i))
        _invariant(_inline_pulse(
            exists* s.
              (Struct_vec.struct_vec__aux_raw_unfolded $(v) 1.0R) **
              (array_pts_to (Struct_vec.struct_vec__data_1 $(v)) 1.0R s) **
              (pure (array_spec_len s == UInt32.v $(n))) **
              (pure (array_spec_full_mask s)) **
              (pure (forall (k: nat). {:pattern (array_spec_initd s k)} k < UInt32.v $(i) ==> array_spec_initd s k))
        ))
    {
        v->data[i] = x;
    }
#endif
    return v;
}
