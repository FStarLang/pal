#include "pal.h"
#include <stdint.h>

/*
 * The byte order is the target's. PAL takes it from clang and states it in
 * the generated `Pulse.Lib.C.Palow.Target`; the library is written against
 * that module's interface and never asks which order it is.
 *
 * This file is translated twice, for one architecture in either order:
 * `byte_order_be` for mips64 and `byte_order_le` for mips64el. Storing the
 * word 0x01020304 and reading the first byte of it back through a
 * `uint8_t[4]` gives 1 on the first and 4 on the second. The contract says
 * which using the preprocessor's own `__BYTE_ORDER__`, so if the order PAL
 * generates disagreed with the one the compiler builds for, this would not
 * verify.
 *
 * The proof comes in two halves, and only one of them knows the order.
 * `w_as_c` re-reads a word as its bytes in whatever order the target stores
 * them: it is a theorem about every target. Saying which of those bytes comes
 * first is the other half, and it needs `TargetFacts.byte_order_is`, which is
 * the one place the order is revealed.
 *
 * `palow-only`: the old model has no bytes to put in an order.
 */

_include_pulse(Byte_order_facts,
  module E = Pulse.Lib.C.Palow.Encoding
  module T = Pulse.Lib.C.Palow.Target
  open Union_word

  (* Byte `k` of `x`, counting from the least significant. *)
  let byte_of (x: UInt32.t) (k: nat) : UInt8.t =
    UInt8.uint_to_t ((UInt32.v x / pow2 (8 * k)) % 256)

  (* The bytes of `x` in the order the target stores them, whichever that is. *)
  let word_bytes (x: UInt32.t) : (s: Seq.seq UInt8.t { Seq.length s == 4 }) =
    Seq.init 4 (fun (i: nat { i < 4 }) -> byte_of x (E.significance T.byte_order 4 i))

  (* The bytes that represent a `uint32_t` are, one at a time, the `uint8_t`s
     `word_bytes` says. This holds on every target, so nothing here asks. *)
  let word_as_bytes (x: UInt32.t) (b: bytes)
    : Lemma (requires uint32_t_repr x b)
            (ensures  array_repr uint8_t_repr 1 (word_bytes x) b)
    = let aux (i: nat { i < 4 })
        : Lemma (uint8_t_repr (Seq.index (word_bytes x) i) (elem_bytes 1 b i))
        = assert_norm (pow2 0 == 1);
          bytes_ext (elem_bytes 1 b i)
                    (E.encode T.byte_order 1 None (UInt8.v (Seq.index (word_bytes x) i)))
      in
      Classical.forall_intro aux

  (* A union holding a word holds the same bytes read as an array. *)
  ghost fn w_as_c (u: ptr) (#p: perm) (#x: UInt32.t)
    requires union_word_pts_to u p (Union_word_w x)
    ensures  union_word_pts_to u p (Union_word_c (word_bytes x))
  {
    unfold union_word_pts_to u p (Union_word_w x);
    (* No parentheses after `assert`: this text is preprocessed, and with them
       it would be a call of the C macro. *)
    with b. assert mem_pts_to u p b;
    word_as_bytes x (slice b 0 4);
    fold union_word_pts_to u p (Union_word_c (word_bytes x));
  }

  (* Byte `k` of 0x01020304 is `4 - k`, on any target. *)
  let byte_of_word (k: nat { k < 4 })
    : Lemma (UInt8.v (byte_of 0x01020304ul k) == 4 - k)
    = assert_norm (pow2 0 == 1 /\ pow2 8 == 256 /\ pow2 16 == 65536 /\ pow2 24 == 16777216)
)

/* Which byte comes first. It follows from asking the target, it does not
 * follow without asking, and the other order's answer is refuted. */
#if __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
_include_pulse(Byte_order_answer,
  module E = Pulse.Lib.C.Palow.Encoding
  module T = Pulse.Lib.C.Palow.Target
  module TF = Pulse.Lib.C.Palow.TargetFacts
  open Byte_order_facts

  let first () : Lemma (UInt8.v (Seq.index (word_bytes 0x01020304ul) 0) == 1)
    = TF.byte_order_is (); byte_of_word (E.significance T.byte_order 4 0)

  [@@expect_failure]
  let unasked () : Lemma (UInt8.v (Seq.index (word_bytes 0x01020304ul) 0) == 1)
    = byte_of_word (E.significance T.byte_order 4 0)

  [@@expect_failure]
  let other () : Lemma (UInt8.v (Seq.index (word_bytes 0x01020304ul) 0) == 4)
    = TF.byte_order_is (); byte_of_word (E.significance T.byte_order 4 0)
)
#else
_include_pulse(Byte_order_answer,
  module E = Pulse.Lib.C.Palow.Encoding
  module T = Pulse.Lib.C.Palow.Target
  module TF = Pulse.Lib.C.Palow.TargetFacts
  open Byte_order_facts

  let first () : Lemma (UInt8.v (Seq.index (word_bytes 0x01020304ul) 0) == 4)
    = TF.byte_order_is (); byte_of_word (E.significance T.byte_order 4 0)

  [@@expect_failure]
  let unasked () : Lemma (UInt8.v (Seq.index (word_bytes 0x01020304ul) 0) == 4)
    = byte_of_word (E.significance T.byte_order 4 0)

  [@@expect_failure]
  let other () : Lemma (UInt8.v (Seq.index (word_bytes 0x01020304ul) 0) == 1)
    = TF.byte_order_is (); byte_of_word (E.significance T.byte_order 4 0)
)
#endif

union word {
  uint32_t w;
  uint8_t c[4];
};

/* Store a word, read its first byte back through the other member. */
_requires(_inline_pulse(union_word_pts_to $(u) 1.0R (Union_word_w 0x01020304ul)))
_ensures(_inline_pulse(union_word_pts_to $(u) 1.0R
                         (Union_word_c (Byte_order_facts.word_bytes 0x01020304ul))))
#if __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
_ensures(return == 1)
#else
_ensures(return == 4)
#endif
uint8_t first_byte(_plain union word *u)
{
  _ghost_stmt(Byte_order_facts.w_as_c $(u));
  _ghost_stmt(Byte_order_answer.first ());
  return u->c[0];
}
