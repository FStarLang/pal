#include "pal.h"
#include <stddef.h>
#include <stdint.h>

// A pure `_refine` on a struct declaration reaches the elements of an `_array`
// of that struct. PAL emits a named predicate `struct_small__refine` in the
// struct's module and, next to `array_pts_to_full a p s`, the fact
// `array_spec_forall struct_small__refine s`: every initialized element
// satisfies the refinement.
//
// The quantifier behind `array_spec_forall` is opaque to SMT. Reads, writes
// and loop invariants use it through patterned lemmas in Pulse.Lib.C.Array,
// so nothing below reveals it by hand.
//
// Negative controls, run by hand (each fails with Error 19 in the named
// function, and only there):
//   N1 write_small with `x < 101`               -> Func_write_small
//   N2 write_small_field without `x < 100`      -> Func_write_small_field
//   N3 read_small ensuring `return < 99`        -> Func_read_small
//   N4 max_small's loop over `struct plain`     -> Func_max_plain
//   N5 `struct small` without its `_refine`     -> Func_read_small, Func_max_small
//   N6 read_hidden without its reveal           -> Func_read_hidden
//   N7 `struct slot` without its pool clause     -> Func_slot_pool
//   N8 the global's `_live` without the element fact (no refinement on the
//      `live_var_slots` predicate)                -> Func_slot_gid

struct _refine(this.v < 100) small {
  uint32_t v;
};

// Reading an element yields the refinement.
uint32_t read_small(_array struct small *a, size_t i)
  _requires(i < a._length)
  _ensures(return < 100)
{
  return a[i].v;
}

// Writing a whole element requires the refinement of the written value; the
// callee's postcondition re-establishes the array fact.
void write_small(_array struct small *a, size_t i, uint32_t x)
  _requires(i < a._length && x < 100)
{
  struct small s = { .v = x };
  a[i] = s;
}

// Writing a field of an element in place (borrow, write, return the cell).
void write_small_field(_array struct small *a, size_t i, uint32_t x)
  _requires(i < a._length && x < 100)
{
  a[i].v = x;
}

// The fact survives a loop invariant that only says the array is live.
uint32_t max_small(_array struct small *a, size_t n)
  _requires(n <= a._length)
  _ensures(return < 100)
{
  uint32_t m = 0;
  for (size_t i = 0; i < n; i++)
    _invariant(_live(*a) && _live(i) && _live(m))
    _invariant(i <= n && n <= a._length && m < 100)
  {
    if (a[i].v > m)
      m = a[i].v;
  }
  return m;
}

// A caller must establish the fact to call a function that assumes it.
uint32_t forward_read(_array struct small *a)
  _requires(a._length == 4)
  _ensures(return < 100)
{
  return read_small(a, 3);
}

// Unrefined structs are unaffected: no element fact, and none needed.
struct plain {
  uint32_t v;
};

uint32_t read_plain(_array struct plain *a, size_t i)
  _requires(i < a._length)
{
  return a[i].v;
}

// A refinement can name an F* predicate through `_inline_pulse`, and should
// when the condition is expensive: an opaque predicate is one uninterpreted
// symbol in every query that carries the refinement, and only a proof that
// needs its meaning pays for it, by revealing it.
_include_pulse(OpaqueBound,
  [@@"opaque_to_smt"]
  let bounded (x: FStar.UInt32.t) : prop = FStar.UInt32.v x < 100

  let reveal (x: FStar.UInt32.t)
  : FStar.Pervasives.Lemma (bounded x <==> FStar.UInt32.v x < 100)
  = FStar.Pervasives.reveal_opaque "OpaqueBound.bounded" (bounded x)
)

struct _refine((_Bool) _inline_pulse(OpaqueBound.bounded $(this.v))) hidden {
  uint32_t v;
};

uint32_t read_hidden(_array struct hidden *a, size_t i)
  _requires(i < a._length)
  _ensures(return < 100)
{
  uint32_t r = a[i].v;
  _ghost_stmt(OpaqueBound.reveal $(r));
  return r;
}

// The fact is carried opaquely through a call: the callee assumes it of its
// by-value argument, and the caller discharges it from the array element
// without ever revealing it.
uint32_t hidden_v(struct hidden h)
{
  return h.v;
}

uint32_t forward_hidden(_array struct hidden *a)
  _requires(a._length == 2)
{
  return hidden_v(a[1]);
}

// A mutable array global of a refined struct: `_live(g)` carries the element
// fact like an `_array` parameter does, so a read through the global yields
// the refinement. Whoever supplies `_live(g)` (in the end an entry point's
// precondition, i.e. an assumption about the initial contents) supplies the
// fact too, and every write through it must keep it.
//
// The refinement may also compare a pointer field with the address of a
// mutable array global: the name of such a global decays to a constant
// handle, so the comparison is a fact about the value alone.
struct item {
  uint32_t v;
};

struct item pool_a[4];
struct item pool_b[4];

struct _refine(this.gid < 4)
       _refine(this.pool == NULL || this.pool == pool_a || this.pool == pool_b)
       slot {
  uint32_t gid;
  struct item *pool;
};

struct slot slots[3];

uint32_t slot_gid(size_t i)
  _requires(i < 3)
  _preserves(_live(slots))
  _ensures(return < 4)
{
  return slots[i].gid;
}

// The pointer can only be one of the two pools: no third case to handle.
int slot_pool(struct slot *s)
  _ensures(return == 0 || return == 1 || return == 2)
{
  if (s->pool == NULL)
    return 0;
  if (s->pool == pool_a)
    return 1;
  _assert(s->pool == pool_b);
  return 2;
}
