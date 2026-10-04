#include "pal.h"
#include <stdint.h>
#include <stddef.h>

/* Reading typed values out of bytes that came from nowhere in particular.
 *
 * A device, a firmware blob or a network peer hands over a range of memory
 * that is known only to be initialised and to hold no pointers. Every one of
 * those byte strings is the representation of *some* value of a structure
 * made of integers -- the encoding is onto -- and `pal` names that value:
 * `struct_T_of_bytes b`, assembled field by field from the integer readers
 * `T_of_bytes`. `struct_T_conceal_bytes` turns the bytes into the structure's
 * points-to at that value, so the claim needs no axiom about the bytes.
 *
 * What the value is depends on the target's byte order, which is the point:
 * the reader is `decode` at `Target.byte_order`, the same order the writer
 * encodes with, and nothing here asks which one it is.
 *
 * `palow-only`: the old model has no bytes to read a value out of. */

_include_pulse(Of_bytes_shim,
  include Pulse.Lib.C.Palow.Ptr
  include Pulse.Lib.C.Palow.Bytes
  include Pulse.Lib.C.Palow
  include Pulse.Lib.C.Palow.Scalar
  include Pulse.Lib.C.Palow.CTypes
  include Pulse.Lib.C.Palow.Array

  (* What arrives from outside: `n` initialised bytes with no provenance,
     placed where a `T` of alignment `al` may live. *)
  unfold let wire (a: ptr) (b: bytes) (n al: FStar.SizeT.t) : slprop =
    mem_pts_to a 1.0R b
    ** pure (len b == FStar.SizeT.v n /\ initialized b /\ no_prov b /\ aligned a al)

  (* A scalar bytes read back as that scalar: the reader is a left inverse
     of the representation, so a value that was ever stored is recovered
     exactly, in either byte order. *)
  ghost fn u32_as_bytes (a: ptr) (#x: UInt32.t)
    requires uint32_t_pts_to a 1.0R x
    ensures  exists* b. mem_pts_to a 1.0R b ** pure (uint32_t_of_bytes b == x)
  {
    uint32_t_reveal a;
    (* No parentheses after `assert`: this text is preprocessed, and with them
       it would be a call of the C macro. *)
    with b. assert mem_pts_to a 1.0R b;
    uint32_t_of_bytes_inverse x b;
    assert pure (uint32_t_of_bytes b == x);
  }
)

_type(bytes_t, Pulse.Lib.C.Palow.Bytes.bytes)

/* Padding after `kind` and nowhere else; a signed field of each width the
 * reader has to sign-extend; and `size_t`, whose width is the target's. */
struct hdr {
  uint8_t  kind;
  int16_t  delta;
  uint32_t len;
  int64_t  stamp;
  size_t   count;
};

/* A structure inside a structure, and tail padding after `code`. */
struct msg {
  struct hdr h;
  int32_t    code;
};

/* Any initialised, pointer-free bytes are a `struct hdr`. The value read back
 * through the claimed structure is the one the bytes decode to. */
_ghost_arg(bytes_t b)
_requires(_inline_pulse(Of_bytes_shim.wire $(h) $(b) struct_hdr_sizeof struct_hdr_alignof))
_ensures(_inline_pulse(struct_hdr_pts_to $(h) 1.0R (struct_hdr_of_bytes $(b))))
_ensures(_inline_pulse(pure ($(return) == (struct_hdr_of_bytes $(b)).fld_len)))
uint32_t hdr_len(_plain struct hdr *h)
{
  _ghost_stmt(struct_hdr_conceal_bytes $(h));
  return h->len;
}

/* The same through a nested field: the inner structure is read out of the
 * outer one's bytes at the inner structure's offset. */
_ghost_arg(bytes_t b)
_requires(_inline_pulse(Of_bytes_shim.wire $(m) $(b) struct_msg_sizeof struct_msg_alignof))
_ensures(_inline_pulse(struct_msg_pts_to $(m) 1.0R (struct_msg_of_bytes $(b))))
_ensures(_inline_pulse(pure ($(return) == (struct_msg_of_bytes $(b)).fld_h.fld_stamp)))
_ensures(_inline_pulse(pure ((struct_msg_of_bytes $(b)).fld_h ==
           struct_hdr_of_bytes (field_bytes $(b) (SizeT.v struct_msg_offsetof_h) (SizeT.v struct_hdr_sizeof)))))
int64_t msg_stamp(_plain struct msg *m)
{
  _ghost_stmt(struct_msg_conceal_bytes $(m));
  return m->h.stamp;
}

/* Ten fields and no padding, the shape of an ELF section header. A proof
 * that put every field in one query would not finish for this; the generated
 * one takes the fields one at a time. */
struct shdr {
  uint32_t sh_name;
  uint32_t sh_type;
  uint64_t sh_flags;
  uint64_t sh_addr;
  uint64_t sh_offset;
  uint64_t sh_size;
  uint32_t sh_link;
  uint32_t sh_info;
  uint64_t sh_addralign;
  uint64_t sh_entsize;
};

_ghost_arg(bytes_t b)
_requires(_inline_pulse(Of_bytes_shim.wire $(s) $(b) struct_shdr_sizeof struct_shdr_alignof))
_ensures(_inline_pulse(struct_shdr_pts_to $(s) 1.0R (struct_shdr_of_bytes $(b))))
_ensures(_inline_pulse(pure ($(return) == (struct_shdr_of_bytes $(b)).fld_sh_entsize)))
uint64_t shdr_entsize(_plain struct shdr *s)
{
  _ghost_stmt(struct_shdr_conceal_bytes $(s));
  return s->sh_entsize;
}

/* An array of structures out of one range of bytes: element `i` is what its
 * own `sizeof(struct hdr)` bytes read as. */
_ghost_arg(bytes_t b)
_requires(_inline_pulse(mem_pts_to $(a) 1.0R $(b)))
_requires(_inline_pulse(pure (len $(b) == SizeT.v struct_hdr_sizeof * 4)))
_requires(_inline_pulse(pure (initialized $(b) /\ no_prov $(b))))
_requires(_inline_pulse(pure (array_aligned (SizeT.v struct_hdr_sizeof)
                                            (SizeT.v struct_hdr_alignof) $(a))))
_ensures(_inline_pulse(array_pts_to struct_hdr_repr (SizeT.v struct_hdr_sizeof)
                         (SizeT.v struct_hdr_alignof) $(a) 1.0R
                         (array_of_bytes struct_hdr_of_bytes (SizeT.v struct_hdr_sizeof) 4 $(b))))
void claim_hdrs(_plain struct hdr *a)
{
  _ghost_stmt(array_of_bytes_repr struct_hdr_repr struct_hdr_of_bytes
                (SizeT.v struct_hdr_sizeof) struct_hdr_of_bytes_repr 4 $(b));
  _ghost_stmt(array_conceal struct_hdr_repr $(a) struct_hdr_sizeof struct_hdr_alignof #1.0R #$(b) #(
                array_of_bytes struct_hdr_of_bytes (SizeT.v struct_hdr_sizeof) 4 $(b)));
}

/* A scalar out of bytes, and back: `uint32_t_of_bytes` is what is loaded, and
 * re-reading the bytes of the loaded word gives the same word. */
_ghost_arg(bytes_t b)
_requires(_inline_pulse(Of_bytes_shim.wire $(p) $(b) uint32_t_sizeof uint32_t_alignof))
_ensures(_inline_pulse(exists* b1. mem_pts_to $(p) 1.0R b1 **
                         pure (uint32_t_of_bytes b1 == uint32_t_of_bytes $(b))))
_ensures(_inline_pulse(pure ($(return) == uint32_t_of_bytes $(b))))
uint32_t load_u32(_plain uint32_t *p)
{
  _ghost_stmt(uint32_t_of_bytes_repr $(b));
  _ghost_stmt(uint32_t_conceal $(p) #1.0R #$(b) #(uint32_t_of_bytes $(b)));
  uint32_t v = *p;
  _ghost_stmt(Of_bytes_shim.u32_as_bytes $(p));
  return v;
}
