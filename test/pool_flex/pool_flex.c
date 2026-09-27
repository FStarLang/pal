#include "pal.h"
#include <stdlib.h>

typedef struct {
    size_t begin, end;
    unsigned char data[];
} pool;

_include_pulse(P,
  include Pulse.Lib.C.Palow.Ptr
  include Pulse.Lib.C.Palow.Bytes
  include Pulse.Lib.C.Palow
  include Pulse.Lib.C.Palow.Scalar
  include Pulse.Lib.C.Palow.Alloc
  include Pulse.Lib.C.Palow.Array
  include Pulse.Lib.C.Palow.Nullable
  include Struct_pool_anon_1

  (* The pool, owned in pieces: the two header fields at their own addresses,
     and the bytes that have not been handed out yet. What has been handed out
     is not mentioned -- it belongs to whoever was handed it, which is exactly
     what makes the chunks independent.

     The indices are `nat`, not `size_t`: an slprop's arguments are typed with
     none of the surrounding `requires` in scope, so `b + n` as a `size_t`
     would carry an overflow obligation nothing could discharge. The `size_t`
     values live under the existential instead, tied to the indices there. *)
  (* The pool with nothing outstanding: what `free` needs back. *)
  unfold let pool_whole (a: ptr) (en: nat) : slprop =
    exists* (b e sz: FStar.SizeT.t) (bs: bytes).
      size_t_pts_to (a +! struct_pool_anon_1_offsetof_begin) 1.0R b **
      size_t_pts_to (a +! struct_pool_anon_1_offsetof_end) 1.0R e **
      struct_pool_anon_1_padding a 1.0R **
      mem_pts_to (a +! struct_pool_anon_1_offsetof_data) 1.0R bs **
      freeable a sz **
      pure (len bs == en
/\ FStar.SizeT.v sz == FStar.SizeT.v struct_pool_anon_1_sizeof + en)

  unfold let pool_inv (a: ptr) (b: FStar.SizeT.t) (en: nat) : slprop =
    exists* (e sz: FStar.SizeT.t) (bs: bytes).
      size_t_pts_to (a +! struct_pool_anon_1_offsetof_begin) 1.0R b **
      size_t_pts_to (a +! struct_pool_anon_1_offsetof_end) 1.0R e **
      struct_pool_anon_1_padding a 1.0R **
      mem_pts_to ((a +! struct_pool_anon_1_offsetof_data) +! b) 1.0R bs **
      freeable a sz **
      pure (FStar.SizeT.v e == en /\ FStar.SizeT.v b <= en
/\ len bs == en - FStar.SizeT.v b
/\ FStar.SizeT.v sz == FStar.SizeT.v struct_pool_anon_1_sizeof + en)
)

_ghost_arg(size_t b)
_ghost_arg(size_t e)
_requires(_inline_pulse(pure (FStar.SizeT.v $(n) <= FStar.SizeT.v $(e) - FStar.SizeT.v $(b))))
_requires(_inline_pulse(P.pool_inv $(p) $(b) (FStar.SizeT.v $(e))))
_ensures(_inline_pulse(
  pure ($(return) == ($(p) +! struct_pool_anon_1_offsetof_data) +! $(b)) **
  (exists* bs. mem_pts_to $(return) 1.0R bs ** pure (len bs == FStar.SizeT.v $(n))) **
  (exists* b2. pure (FStar.SizeT.v b2 == FStar.SizeT.v $(b) + FStar.SizeT.v $(n))
               ** P.pool_inv $(p) b2 (FStar.SizeT.v $(e)))))
void *pool_alloc(_plain pool *p, size_t n)
{
    if (n > p->end - p->begin) {
        /* Unreachable: the contract promises the pool has room. */
        _ghost_stmt(unreachable ());
        return NULL;
    }
    void *x = &p->data[p->begin];
    _ghost_stmt(mem_split (($(p) +! struct_pool_anon_1_offsetof_data) +! $(b)) $(n));
    p->begin += n;
    /* The chunk handed out sits at `(data + b) + n`, and the contract says
       `data + (b + n)`. The SMT pattern proves them equal; the rewrite is
       what makes Pulse's syntactic matcher use it. */
    _ghost_stmt(rewrite each ((($(p) +! struct_pool_anon_1_offsetof_data) +! $(b)) +! $(n))
                as (($(p) +! struct_pool_anon_1_offsetof_data) +! ($(b) `FStar.SizeT.add` $(n))));
    return x;
}

_requires(_inline_pulse(pure (FStar.SizeT.fits (16 + FStar.SizeT.v $(max_alloc)))))
_ensures(_inline_pulse(unless_null $(return)
  (P.pool_inv $(return) 0sz (FStar.SizeT.v $(max_alloc)))))
pool *pool_new(size_t max_alloc)
{
    pool *p = malloc(sizeof(pool) + max_alloc);
    if (!p) return NULL;
    p->begin = 0;
    p->end = max_alloc;
    /* The unclaimed range starts at `data + 0`, and `data` is what the array
       was given up at. Both introductions are `[@@pulse_intro]`, so which one
       applies has to be said. */
    _ghost_stmt(rewrite each ($(p) +! struct_pool_anon_1_offsetof_data)
                as (($(p) +! struct_pool_anon_1_offsetof_data) +! 0sz));
    _ghost_stmt(intro_unless_null $(p)
                (P.pool_inv $(p) 0sz (FStar.SizeT.v $(max_alloc))));
    return p;
}

_ghost_arg(size_t max_alloc)
_requires(_inline_pulse(pure (FStar.SizeT.fits (16 + FStar.SizeT.v $(max_alloc)))))
_requires(_inline_pulse(P.pool_whole $(p) (FStar.SizeT.v $(max_alloc))))
void pool_free(_plain pool *p)
{
    /* Put the pool back together: the two header objects become the bytes
       they stand for, and the three ranges join into the one block `free`
       was given. Only the author knows everything has come back, so this is
       the author's step. */
    _ghost_stmt(unfold struct_pool_anon_1_padding $(p) 1.0R);
    _ghost_stmt(size_t_reveal ($(p) +! struct_pool_anon_1_offsetof_begin));
    _ghost_stmt(size_t_reveal ($(p) +! struct_pool_anon_1_offsetof_end));
    _ghost_stmt(rewrite each ($(p) +! struct_pool_anon_1_offsetof_begin) as $(p));
    _ghost_stmt(mem_join $(p) 8sz);
    _ghost_stmt(mem_join $(p) 16sz);
    free(p);
}

