/* A pool allocator on a flexible array member, and a client that uses it.

   The pool owns storage it hands out, which is the first thing the generated
   `struct_S_pts_to` cannot describe: that predicate is one slprop over the
   whole object, and after the first hand-out no single term says what is left.
   So the contract owns the struct in pieces -- the header fields at their own
   addresses, and the bytes nobody has been given -- and the emitter reads that
   off the contract rather than off an annotation. See palow.md milestone 14. */
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

  (* How much of the pool one allocation of `n` bytes actually consumes.
     A pool that hands out objects of every type has to hand out suitably
     aligned addresses, and `max_align` is what suitably aligned means; so the
     cursor moves by `n` rounded up to a multiple of it, never by `n`.
     Written with addition and remainder rather than a division and a
     multiplication because no multiplication operator is in scope in a
     generated module. *)
  unfold let roundup (n: FStar.SizeT.t) : GTot nat =
    FStar.SizeT.v n + (16 - FStar.SizeT.v n % 16) % 16

  (* The bytes between the end of a chunk and the start of the next one. They
     belong to whoever holds the chunk -- the pool has moved past them -- so
     they come back with it. *)
  let pad ([@@@mkey] a: ptr) (n: FStar.SizeT.t) : slprop =
    exists* bs. mem_pts_to (a +! n) 1.0R bs
                ** pure (len bs == roundup n - FStar.SizeT.v n)

  (* The `r` bytes at `a` that have been given back to the pool. Opaque, so
     that `r` is something the Pulse matcher can solve for: a quantity tied to
     the state only by a `pure` equation is not one a caller could ever infer.
     The `mkey` on `a` is what makes the matcher key on the address. *)
  let returned ([@@@mkey] a: ptr) (r: FStar.SizeT.t) : slprop =
    exists* rs. mem_pts_to a 1.0R rs ** pure (len rs == FStar.SizeT.v r)

  (* The pool, owned in pieces.

     `b` is what `begin` holds, `e` what `end` holds, and `r` is how much has
     been given back. The first `r` bytes belong to the pool again, the bytes
     from `r` up to `b` are out with whoever was handed them, and the bytes
     from `b` on have never been given to anyone. Naming the returned prefix
     is what lets the pool be freed: a pool with `r == b` owns all of its
     storage again, and nothing short of that does.

     Every index is a `size_t` held by a points-to, so that a caller can infer
     it by matching rather than from a `pure` fact. *)
  unfold let pool_inv (a: ptr) (b r e: FStar.SizeT.t) : slprop =
    exists* (sz: FStar.SizeT.t) (bs: bytes).
      size_t_pts_to (a +! struct_pool_anon_1_offsetof_begin) 1.0R b **
      size_t_pts_to (a +! struct_pool_anon_1_offsetof_end) 1.0R e **
      struct_pool_anon_1_padding a 1.0R **
      returned (a +! struct_pool_anon_1_offsetof_data) r **
      mem_pts_to ((a +! struct_pool_anon_1_offsetof_data) +! b) 1.0R bs **
      freeable a sz **
      pure (FStar.SizeT.v b <= FStar.SizeT.v e
/\ len bs == FStar.SizeT.v e - FStar.SizeT.v b
/\ FStar.SizeT.v r <= FStar.SizeT.v b
/\ aligned a max_align
/\ FStar.SizeT.v b % 16 == 0
/\ FStar.SizeT.v sz == FStar.SizeT.v struct_pool_anon_1_sizeof + FStar.SizeT.v e)

  (* Give a chunk back. There is no C function for this -- a bump allocator
     has no `pool_free_one` -- so it is a ghost step, and what entitles the
     caller to take it is that the chunk starts where the returned prefix
     ends. *)
  ghost fn pool_return (a: ptr) (r: FStar.SizeT.t)
                       (n: FStar.SizeT.t { FStar.SizeT.fits (FStar.SizeT.v r + FStar.SizeT.v n) })
                       (#b #e: FStar.SizeT.t) (#c: bytes)
    requires pool_inv a b r e
    requires mem_pts_to ((a +! struct_pool_anon_1_offsetof_data) +! r) 1.0R c
    requires pure (len c == FStar.SizeT.v n
/\ FStar.SizeT.v r + FStar.SizeT.v n <= FStar.SizeT.v b)
    ensures  pool_inv a b (r `FStar.SizeT.add` n) e
  {
    unfold returned (a +! struct_pool_anon_1_offsetof_data) r;
    mem_join (a +! struct_pool_anon_1_offsetof_data) r;
    fold returned (a +! struct_pool_anon_1_offsetof_data) (r `FStar.SizeT.add` n);
  }
)

_requires(_inline_pulse(pure (FStar.SizeT.fits (16 + FStar.SizeT.v $(max_alloc)))))
_ensures(_inline_pulse(unless_null $(return)
  (P.pool_inv $(return) 0sz 0sz $(max_alloc))))
pool *pool_new(size_t max_alloc)
{
    pool *p = malloc(sizeof(pool) + max_alloc);
    if (!p) return NULL;
    p->begin = 0;
    p->end = max_alloc;
    /* Nothing has been handed out, so the returned prefix is empty and the
       unclaimed range is all of it. Splitting at zero says both at once. */
    _ghost_stmt(mem_split ($(p) +! struct_pool_anon_1_offsetof_data) 0sz);
    _ghost_stmt(fold P.returned ($(p) +! struct_pool_anon_1_offsetof_data) 0sz);
    /* Both `unless_null` introductions are `[@@pulse_intro]`, so which one
       applies has to be said. */
    _ghost_stmt(intro_unless_null $(p)
                (P.pool_inv $(p) 0sz 0sz $(max_alloc)));
    return p;
}

_ghost_arg(size_t b)
_ghost_arg(size_t r)
_ghost_arg(size_t e)
_requires(_inline_pulse(pure (P.roundup $(n) <= FStar.SizeT.v $(e) - FStar.SizeT.v $(b))))
_requires(_inline_pulse(P.pool_inv $(p) $(b) $(r) $(e)))
_ensures(_inline_pulse(
  pure ($(return) == ($(p) +! struct_pool_anon_1_offsetof_data) +! $(b)) **
  pure (aligned $(return) max_align) **
  (exists* bs. mem_pts_to $(return) 1.0R bs ** pure (len bs == FStar.SizeT.v $(n))) **
  P.pad $(return) $(n) **
  (exists* b2. pure (FStar.SizeT.v b2 == FStar.SizeT.v $(b) + P.roundup $(n))
               ** P.pool_inv $(p) b2 $(r) $(e))))
void *pool_alloc(_plain pool *p, size_t n)
{
    if (n > p->end - p->begin) {
        /* Unreachable: the contract promises the pool has room. */
        _ghost_stmt(unreachable ());
        return NULL;
    }
    void *x = &p->data[p->begin];
    /* The cursor moves by the rounded size, so that the next chunk starts on
       a `max_align` boundary just as this one did. Declared after the early
       return so that the unreachable branch has nothing to give back. */
    size_t m = n + (16 - n % 16) % 16;
    /* The chunk is aligned because the data area is and the cursor is a
       multiple of `max_align`. */
    _ghost_stmt(aligned_add $(p) max_align struct_pool_anon_1_offsetof_data);
    _ghost_stmt(aligned_add ($(p) +! struct_pool_anon_1_offsetof_data) max_align $(b));
    /* The slot is `m` bytes: `n` for the caller and the rest for the pad. */
    _ghost_stmt(mem_split (($(p) +! struct_pool_anon_1_offsetof_data) +! $(b)) $(m));
    _ghost_stmt(mem_split (($(p) +! struct_pool_anon_1_offsetof_data) +! $(b)) $(n));
    _ghost_stmt(fold P.pad (($(p) +! struct_pool_anon_1_offsetof_data) +! $(b)) $(n));
    p->begin += m;
    /* The chunk handed out sits at `(data + b) + n`, and the contract says
       `data + (b + n)`. The SMT pattern proves them equal; the rewrite is
       what makes the syntactic matcher in Pulse use it. */
    _ghost_stmt(rewrite each ((($(p) +! struct_pool_anon_1_offsetof_data) +! $(b)) +! $(m))
                as (($(p) +! struct_pool_anon_1_offsetof_data) +! ($(b) `FStar.SizeT.add` $(m))));
    return x;
}

_ghost_arg(size_t b)
_ghost_arg(size_t max_alloc)
_requires(_inline_pulse(pure (FStar.SizeT.fits (16 + FStar.SizeT.v $(max_alloc)))))
_requires(_inline_pulse(P.pool_inv $(p) $(b) $(b) $(max_alloc)))
void pool_free(_plain pool *p)
{
    /* Put the pool back together. Everything handed out has come back -- that
       is what `r == b` in the precondition says -- so the returned prefix and
       the unclaimed range are the whole tail, the two header objects become
       the bytes they stand for, and the three ranges join into the one block
       `free` was given. */
    _ghost_stmt(unfold P.returned ($(p) +! struct_pool_anon_1_offsetof_data) $(b));
    _ghost_stmt(mem_join ($(p) +! struct_pool_anon_1_offsetof_data) $(b));
    _ghost_stmt(unfold struct_pool_anon_1_padding $(p) 1.0R);
    _ghost_stmt(size_t_reveal ($(p) +! struct_pool_anon_1_offsetof_begin));
    _ghost_stmt(size_t_reveal ($(p) +! struct_pool_anon_1_offsetof_end));
    _ghost_stmt(rewrite each ($(p) +! struct_pool_anon_1_offsetof_begin) as $(p));
    _ghost_stmt(mem_join $(p) 8sz);
    _ghost_stmt(mem_join $(p) 16sz);
    free(p);
}

void example()
{
    pool *p = pool_new(1024);
    /* `pool_new` wrote its own `unless_null`, so the null test spends it by
       hand: the emitter only knows how to spend a guard it wrote itself. */
    if (!p) {
        _ghost_stmt(elim_unless_null_null $(p) (P.pool_inv $(p) 0sz 0sz 1024sz));
        return;
    }
    _ghost_stmt(elim_unless_null $(p) (P.pool_inv $(p) 0sz 0sz 1024sz));
    int *x = pool_alloc(p, sizeof(int));
    long *y = pool_alloc(p, sizeof(long));
    *x = 6;
    *y = *x;
    /* Hand both chunks back before the pool goes. The pointers are the ones
       `pool_alloc` promised, which is what the two rewrites say. */
    _ghost_stmt(int32_t_reveal $(x));
    _ghost_stmt(unfold P.pad $(x) 4sz);
    _ghost_stmt(mem_join $(x) 4sz);
    _ghost_stmt(rewrite each $(x)
                as (($(p) +! struct_pool_anon_1_offsetof_data) +! 0sz));
    _ghost_stmt(P.pool_return $(p) 0sz 16sz);
    _ghost_stmt(int64_t_reveal $(y));
    /* The second chunk is at `data + 16`, and the pool says so as a `size_t`
       whose value is 16. Naming the address before the rewrite is what keeps
       the equality query small enough to go through. */
    _ghost_stmt(assert pure ($(y) == (($(p) +! struct_pool_anon_1_offsetof_data)
                                      +! 16sz)));
    _ghost_stmt(unfold P.pad $(y) 8sz);
    _ghost_stmt(mem_join $(y) 8sz);
    _ghost_stmt(rewrite each $(y)
                as (($(p) +! struct_pool_anon_1_offsetof_data) +! 16sz));
    _ghost_stmt(P.pool_return $(p) 16sz 16sz);
    pool_free(p);
}
