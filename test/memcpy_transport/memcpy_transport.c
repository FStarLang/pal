#include "pal.h"
#include <stdint.h>
#include <stddef.h>

/* Acceptance test 5 from `palow.md`: a `memcpy` between two objects of
 * different types, with the results related at both types -- including
 * transporting a stored pointer's provenance through the copy.
 *
 * `memcpy` is the one place C is explicit that an object is a sequence of
 * bytes, and it is the reason layer 0 is stated in bytes at all. Its contract
 * says only that the destination ends up holding the *same bytes* as the
 * source: nothing about types, nothing about pointers, nothing about
 * provenance. Everything below falls out of that.
 *
 * The pointer case is the one that would have sunk the design. Under a model
 * where an object representation is a sequence of plain `uint8_t`s, the bytes
 * at the destination determine an address but not which allocation it belongs
 * to, so the recovered pointer has nothing to license a dereference and
 * `transport` is simply not provable. Putting provenance in `byte` closes that
 * gap, and it costs `memcpy`'s specification nothing.
 *
 * `palow-only`: the old model has no byte-level view to state any of this in.
 * The C is still compiled, which is what keeps the annotations honest as
 * no-ops. */

_include_pulse(Copy_shim,
  include Pulse.Lib.C.Palow.Ptr
  include Pulse.Lib.C.Palow.Bytes
  include Pulse.Lib.C.Palow
  include Pulse.Lib.C.Palow.Scalar

  (* Storage of a given size and no particular type: what the destination of a
     copy is before the copy, and the only thing said about it. *)
  unfold let raw (a: ptr) (n: FStar.SizeT.t) : slprop =
    exists* b. mem_pts_to a 1.0R b ** pure (len b == FStar.SizeT.v n)
)

_type(bytes_t, Pulse.Lib.C.Palow.Bytes.bytes)

/* C's `memcpy`, declared with the contract the model gives it. It is assumed
 * here for the same reason it is axiomatized in
 * `Pulse.Lib.C.Palow.Machine`: it is a primitive, not something a C program
 * derives. What matters is that the contract is the one anybody would have
 * written -- same bytes at the destination -- and that nothing below adds to
 * it. */
_ghost_arg(bytes_t bs)
_ghost_arg(bytes_t bd)
_requires(_inline_pulse(mem_pts_to $(src) 1.0R $(bs) ** mem_pts_to $(dst) 1.0R $(bd)))
_requires(_inline_pulse(pure (len $(bs) == FStar.SizeT.v $(n) /\ len $(bd) == FStar.SizeT.v $(n))))
_ensures(_inline_pulse(mem_pts_to $(src) 1.0R $(bs) ** mem_pts_to $(dst) 1.0R $(bs)))
void mem_copy(_plain uint8_t *dst, _plain const uint8_t *src, size_t n);

/* A `uint32_t` copied into storage of no type at all, and read back out of the
 * destination as a `uint32_t`. The destination is related at both types: as
 * bytes, which is all `mem_copy` promises, and as an object, which is what
 * `uint32_t_conceal` turns those bytes into. Neither claim is an axiom -- the
 * bytes at the destination are the source's, and the source's bytes are a
 * representation of its value by definition. */
_ghost_arg(uint32_t x)
_requires(_inline_pulse(uint32_t_pts_to $(src) 1.0R $(x)))
_requires(_inline_pulse(Copy_shim.raw $(dst) uint32_t_sizeof))
_ensures(_inline_pulse(uint32_t_pts_to $(src) 1.0R $(x)))
_ensures(_inline_pulse(uint32_t_pts_to $(dst) 1.0R $(x)))
_ensures(return == x)
uint32_t copy_scalar(_plain uint32_t *dst, _plain const uint32_t *src)
{
  _ghost_stmt(uint32_t_reveal $(src));
  mem_copy((uint8_t *) dst, (const uint8_t *) src, sizeof(uint32_t));
  _ghost_stmt(uint32_t_conceal $(src) #1.0R #_ #$(x));
  _ghost_stmt(uint32_t_conceal $(dst) #1.0R #_ #$(x));
  return *dst;
}

/* And the pointer case. `src` holds a pointer to a `uint32_t`; `dst` is
 * pointer-sized storage of no particular type. After the copy the pointer read
 * back out of `dst` is still dereferenceable -- the dereference at the end is
 * the whole claim -- and `ptr_read`'s `rewrites_to` means the C never has to
 * say that it is the same pointer, because it is.
 *
 * Note that `mem_copy` was told nothing about pointers. */
_ghost_arg(uint32_t x)
_requires(_inline_pulse(ptr_pts_to $(src) 1.0R $(target)))
_requires(_inline_pulse(Copy_shim.raw $(dst) ptr_sizeof))
_requires(_inline_pulse(uint32_t_pts_to $(target) 1.0R $(x)))
_ensures(_inline_pulse(ptr_pts_to $(src) 1.0R $(target)))
_ensures(_inline_pulse(ptr_pts_to $(dst) 1.0R $(target)))
_ensures(_inline_pulse(uint32_t_pts_to $(target) 1.0R $(x)))
_ensures(return == x)
uint32_t transport(_plain uint32_t **src, _plain uint32_t **dst, _plain uint32_t *target)
{
  _ghost_stmt(ptr_reveal $(src));
  mem_copy((uint8_t *) dst, (const uint8_t *) src, sizeof(uint32_t *));
  _ghost_stmt(ptr_conceal $(src) #1.0R #_ #$(target));
  _ghost_stmt(ptr_conceal $(dst) #1.0R #_ #$(target));
  uint32_t *p = *dst;
  return *p;
}
