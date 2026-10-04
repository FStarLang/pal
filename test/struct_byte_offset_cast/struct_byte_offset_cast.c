#include "pal.h"
#include <stddef.h>
#include <stdint.h>

// `(T2 *)((uint8_t *)p + n)`: the object found n bytes past p, the usual C
// idiom for "the record that follows this header in the same buffer". The
// byte cast is kept and lowered as arithmetic on a byte view of p's raw
// address, and the result is retyped through that address. Neither step
// carries ownership: whoever reads through the result must own it.

typedef struct Header { uint32_t Signature; uint32_t Version; } Header;
typedef struct Trailer { uint64_t Crc; } Trailer;

void note_trailer(_plain const Trailer *t);

_include_pulse(StructByteOffsetCast,
  // What the lowering produces, spelled by hand: reading the trailer through
  // the computed address, with only the header owned, must fail.
  [@@expect_failure]
  fn read_without_ownership (h: ref Typedef_Header.ty_header)
    (#v: erased Typedef_Header.ty_header)
    requires Pulse.Lib.Reference.pts_to h v
    returns r: Typedef_Trailer.ty_trailer
    ensures Pulse.Lib.Reference.pts_to h v
  {
    let a = array_to_arrayptr
      (Pulse.Lib.C.Array.ref_to_array #Typedef_uint8_t.ty_uint8_t
        (Pulse.Lib.C.CoreRef.core_to_ref Typedef_uint8_t.ty_uint8_t
          (Pulse.Lib.C.CoreRef.ref_to_core h)))
      8sz;
    arrayptr_drop a;
    let t = Pulse.Lib.C.CoreRef.core_to_ref Typedef_Trailer.ty_trailer
      (Pulse.Lib.C.CoreRef.ref_to_core (Pulse.Lib.C.Array.array_to_ref a));
    !t
  }
)

// Forward from a struct pointer.
void trailer_after(const Header *header)
{
    note_trailer((const Trailer *)((const uint8_t *)header + sizeof(Header)));
}

// Through a local, from a non-const pointer.
void trailer_after_local(Header *header)
{
    const Trailer *trailer = (const Trailer *)((uint8_t *)header + sizeof(Header));
    note_trailer(trailer);
}

// From a byte buffer: the record at a byte offset.
void trailer_in_bytes(_array const uint8_t *bytes, size_t off)
{
    note_trailer((const Trailer *)(bytes + off));
}

// From an array of structs, past its first element.
void trailer_after_first(_array const Header *headers)
{
    note_trailer((const Trailer *)((const uint8_t *)headers + sizeof(Header)));
}
