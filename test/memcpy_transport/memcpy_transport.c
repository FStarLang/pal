#include "pal.h"
#include <stdint.h>
#include <stddef.h>

/* Acceptance test 5 from `palow.md`: a `memcpy` between two objects of
 * different types, with the results related at both types -- including
 * transporting a stored pointer's provenance through the copy.
 *
 * `memcpy` is the one place C is explicit that an object is a sequence of
 * bytes, and it is the reason layer 0 is stated in bytes at all. Its checked
 * contract transports the source bytes and their effective type, while
 * retaining destination declared origin. It says nothing pointer-specific;
 * the provenance transport follows from equality of the copied bytes.
 *
 * The pointer case is the one that would have sunk the design. Under a model
 * where an object representation is a sequence of plain `uint8_t`s, the bytes
 * at the destination determine an address but not which allocation it belongs
 * to, so the recovered pointer has nothing to license a dereference and
 * `transport` is simply not provable. Putting provenance in `byte` closes that
 * gap, and it costs `memcpy`'s specification nothing. */

_include_pulse(Copy_shim,
  include Pulse.Lib.C.Palow.Ptr
  include Pulse.Lib.C.Palow.Bytes
  include Pulse.Lib.C.Palow
  include Pulse.Lib.C.Palow.Scalar
  module ET = Pulse.Lib.C.Palow.Etype

  let copied_index (dst src: ET.etypes) : ET.etypes =
    if ET.elen dst = ET.elen src then
      FStar.Seq.init (ET.elen dst)
        (fun k -> ET.copy_entry (ET.eget dst k) (ET.eget src k))
    else dst

  (* Storage of a given size and no particular type: what the destination of a
     copy is before the copy, and the only thing said about it. *)
  (* The alignment is an argument because copied bytes carry none: `mem_copy`
     promises the destination the source's bytes and nothing else, so whoever
     is going to claim the destination at a type has to have said, in advance,
     that it is aligned for that type. *)
  unfold let raw (a: ptr) (n al: FStar.SizeT.t) : slprop =
    exists* b. mem_pts_to_at a 1.0R b (ET.etypes_none (FStar.SizeT.v n))
               ** pure (len b == FStar.SizeT.v n /\ aligned a al)

  (* The conservative checked-copy model requires an established whole source,
     not just fallback readability or a slice of an enclosing aggregate. *)
  unfold let source (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
      (al: FStar.SizeT.t) (a: ptr) (x: t) : slprop =
    exists* b e. mem_pts_to_at a 1.0R b e **
      pure (repr x b /\ len b == ET.csize ct /\ ET.elen e == len b
        /\ aligned a al /\ ET.read_ok e ct /\ ET.established_type e ct)
)

_type(bytes_t, Pulse.Lib.C.Palow.Bytes.bytes)
_type(etypes_t, Pulse.Lib.C.Palow.Etype.etypes)

/* C's `memcpy`, declared with the checked contract the model gives it. It is assumed
 * here for the same reason it is axiomatized in
 * `Pulse.Lib.C.Palow.Machine`: it is a primitive, not something a C program
 * derives. What matters is that the contract is the one anybody would have
 * written -- same bytes at the destination -- with actual source-derived
 * effective metadata, not a fresh type selected by the caller. */
_ghost_arg(bytes_t bs)
_ghost_arg(bytes_t bd)
_ghost_arg(etypes_t es)
_ghost_arg(etypes_t ed)
_requires(_inline_pulse(mem_pts_to_at $(src) 1.0R $(bs) $(es) **
  mem_pts_to_at $(dst) 1.0R $(bd) $(ed)))
_requires(_inline_pulse(pure (len $(bs) == FStar.SizeT.v $(n) /\ len $(bd) == FStar.SizeT.v $(n))))
_requires(_inline_pulse(pure (ET.elen $(es) == len $(bs) /\ ET.elen $(ed) == len $(bd)
  /\ ET.copy_complete_ok (ET.Ready $(ed)) (ET.Ready $(es)))))
_ensures(_inline_pulse(mem_pts_to_at $(src) 1.0R $(bs) $(es) **
  mem_pts_to_at $(dst) 1.0R $(bs)
    (Copy_shim.copied_index $(ed) $(es))))
void mem_copy(_plain uint8_t *dst, _plain const uint8_t *src, size_t n);

/* A whole established `uint32_t` copied into storage of no type at all, and read back out of the
 * destination as a `uint32_t`. The destination is related at both types: as
 * bytes, which is all `mem_copy` promises, and as an object, which is what
 * `uint32_t_conceal` turns those bytes into. Neither claim is an axiom -- the
 * bytes at the destination are the source's, and the source's bytes are a
 * representation of its value by definition. */
_ghost_arg(uint32_t x)
_requires(_inline_pulse(Copy_shim.source uint32_t_ctype uint32_t_repr
  uint32_t_alignof $(src) $(x)))
_requires(_inline_pulse(Copy_shim.raw $(dst) uint32_t_sizeof uint32_t_alignof))
_ensures(_inline_pulse(uint32_t_pts_to $(src) 1.0R $(x)))
_ensures(_inline_pulse(uint32_t_pts_to $(dst) 1.0R $(x)))
_ensures(return == x)
uint32_t copy_scalar(_plain uint32_t *dst, _plain const uint32_t *src)
{
  _ghost_stmt(unfold Copy_shim.source uint32_t_ctype uint32_t_repr
    uint32_t_alignof $(src) $(x));
  _ghost_stmt(with bs es. assert mem_pts_to_at $(src) 1.0R bs es);
  _ghost_stmt(unfold Copy_shim.raw $(dst) uint32_t_sizeof uint32_t_alignof);
  _ghost_stmt(with bd. assert mem_pts_to_at $(dst) 1.0R bd (ET.etypes_none 4));
  mem_copy((uint8_t *) dst, (const uint8_t *) src, sizeof(uint32_t));
  _ghost_stmt(Pulse.Lib.C.Palow.Copy.copy_read_ok (ET.etypes_none 4) es uint32_t_ctype);
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
_requires(_inline_pulse(Copy_shim.source ptr_ctype ptr_repr ptr_alignof $(src) $(target)))
_requires(_inline_pulse(Copy_shim.raw $(dst) ptr_sizeof ptr_alignof))
_requires(_inline_pulse(uint32_t_pts_to $(target) 1.0R $(x)))
_ensures(_inline_pulse(ptr_pts_to $(src) 1.0R $(target)))
_ensures(_inline_pulse(ptr_pts_to $(dst) 1.0R $(target)))
_ensures(_inline_pulse(uint32_t_pts_to $(target) 1.0R $(x)))
_ensures(return == x)
uint32_t transport(_plain uint32_t **src, _plain uint32_t **dst, _plain uint32_t *target)
{
  _ghost_stmt(unfold Copy_shim.source ptr_ctype ptr_repr ptr_alignof $(src) $(target));
  _ghost_stmt(with bs es. assert mem_pts_to_at $(src) 1.0R bs es);
  _ghost_stmt(unfold Copy_shim.raw $(dst) ptr_sizeof ptr_alignof);
  _ghost_stmt(with bd. assert mem_pts_to_at $(dst) 1.0R bd
    (ET.etypes_none (FStar.SizeT.v ptr_sizeof)));
  mem_copy((uint8_t *) dst, (const uint8_t *) src, sizeof(uint32_t *));
  _ghost_stmt(Pulse.Lib.C.Palow.Copy.copy_read_ok
    (ET.etypes_none (FStar.SizeT.v ptr_sizeof)) es ptr_ctype);
  _ghost_stmt(ptr_conceal $(src) #1.0R #_ #$(target));
  _ghost_stmt(ptr_conceal $(dst) #1.0R #_ #$(target));
  uint32_t *p = *dst;
  return *p;
}
