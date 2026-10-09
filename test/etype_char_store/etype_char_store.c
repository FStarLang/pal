#include "pal.h"
#include <stdint.h>

/* 6.5p6, last sentence: a store through a *character* lvalue does not give
 * the storage an effective type.
 *
 * This is the one place where the "a store types the storage" rule has an
 * explicit exception, and it is load-bearing rather than a curiosity. Byte
 * copies, `memset`, and every hand-written `unsigned char *` loop write
 * through character lvalues. If those writes typed the storage as `char`,
 * then `malloc` + `memset(p, 0, n)` + use-as-`int32_t` -- which is about as
 * ordinary as C gets -- would become undefined, because the storage would
 * now have effective type `char` and `access_ok char 4`-wide-read is false.
 *
 * So this test is a *positive* one: it requires that writing a character into
 * untyped storage leaves it untyped, and therefore still readable at a wider
 * type. It is load-bearing in the mutation sense: replace the `u = tchar`
 * short-circuit in `store_entry` with `false` and the two `store_char_*`
 * lemmas this test leans on stop verifying, because byte 0 would then carry
 * `SChar` and no 4-byte read could cross it.
 *
 * What this test adds over those lemmas is that the exception survives the
 * trip through memory: it is `mem_store_etypes` at `tchar` on a *slice* of a
 * larger object, rejoined, and the enclosing object is still intact.
 *
 * The companion direction -- that a character store does not *destroy* an
 * effective type either -- is `char_store_preserves_declared`.
 *
 * `palow-only`: the old model has no index to state this against. */

_include_pulse(Etype_char_store_include,
  include Pulse.Lib.C.Palow.Ptr
  include Pulse.Lib.C.Palow.Bytes
  include Pulse.Lib.C.Palow
  module E = Pulse.Lib.C.Palow.Etype
  module SZ = FStar.SizeT

  let ct_i32 : E.ctype = E.TScalar E.SInt32

  (* The same obligation `etype_pun_bad` fails to discharge, and the same one
     `etype_access_ok` discharges. *)
  ghost fn read_at (a: ptr) (#p: perm) (#b: bytes) (#e: E.etypes) (u: E.ctype)
    preserves mem_pts_to_at a p b e
    requires  pure (E.read_ok e u)
  {
    ()
  }

  (* [DEFINED] allocated storage, one byte of it written through a character
     lvalue, is still untyped afterwards -- so the whole four bytes may still
     be read as an `int32_t`. This is `malloc` + a byte write + use. *)
  ghost fn char_store_keeps_none (a: ptr) (#b: bytes { len b == 4 })
    requires mem_pts_to_at a 1.0R b (E.etypes_none 4)
    ensures  exists* b2 e2. mem_pts_to_at a 1.0R b2 e2 ** pure (E.read_ok e2 ct_i32)
  {
    mem_split_at a 1sz;

    (* the character store: this is where the 6.5p6 exception applies *)
    mem_store_etypes a E.tchar;

    mem_join_at a 1sz;

    Seq.lemma_eq_intro (Seq.slice (E.etypes_none 4) 0 1) (E.etypes_none 1);
    E.store_char_keeps_none ();
    Seq.lemma_eq_intro
      (Seq.append (E.store_etypes (Seq.slice (E.etypes_none 4) 0 1) E.tchar)
                  (Seq.slice (E.etypes_none 4) 1 4))
      (E.etypes_none 4);

    (* the payoff: the storage is still untyped, so a 4-byte read is fine *)
    read_at a ct_i32
  }

  (* [DEFINED] the other direction: a character store into a *declared*
     `int32_t` does not disturb its effective type either, so the object is
     still readable at `int32_t`. Without the exception this would retype
     byte 0 and the object would become unreadable at its own declared type --
     which would make a byte-wise write into a declared int undefined. *)
  ghost fn char_store_preserves_declared (a: ptr) (#b: bytes { len b == 4 })
    requires mem_pts_to_at a 1.0R b (E.etypes_of ct_i32 true)
    ensures  exists* b2 e2. mem_pts_to_at a 1.0R b2 e2 ** pure (E.read_ok e2 ct_i32)
  {
    mem_split_at a 1sz;
    mem_store_etypes a E.tchar;
    mem_join_at a 1sz;

    E.store_char_identity (Seq.slice (E.etypes_of ct_i32 true) 0 1);
    Seq.lemma_eq_intro
      (Seq.append (E.store_etypes (Seq.slice (E.etypes_of ct_i32 true) 0 1) E.tchar)
                  (Seq.slice (E.etypes_of ct_i32 true) 1 4))
      (E.etypes_of ct_i32 true);

    read_at a ct_i32
  }
)

/* The whole test is in the Pulse block above; a translated C function has to
 * exist for there to be a module to put it in. */
int32_t identity(int32_t x)
  _ensures(_old(x) == x)
{
    return x;
}
