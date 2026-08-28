#include "pal.h"
#include <stdint.h>
#include <stdlib.h>

/* `_ghost_arg` on a function whose address is taken.

   The `__fp` wrapper binds each ghost from the erased witness `c`, which is
   widened from the elim tuple alone to `(elims & ghosts)`:

     Funcptr_impl_one.fsti   (y_fp: erased (unit & ty_int32_t))
                             let var_v = snd (reveal y_fp)

   An indirect call site has no callee declaration, so it can only learn the
   ghost arity from the type written in `struct ops` -- hence the `_ghost_arg`
   annotations on the fields. It then emits `hide (elims, (_, .., _))`: values
   on the elim side, holes on the ghost side, and the tuple spine written out,
   since Pulse solves a hole standing for a tuple leaf but not one standing for
   a whole tuple. */

/* One ghost argument. It occurs inside an slprop, so it is recoverable by
   matching against the caller's context. */
_ghost_arg(int32_t v)
_preserves(_inline_pulse(Pulse.Lib.Reference.pts_to $(q) #1.0R $(v)))
int32_t impl_one(_plain int32_t *q) { return 0; }

/* Two ghost arguments, each pinned by its own slprop. */
_ghost_arg(int32_t v)
_ghost_arg(int32_t w)
_preserves(_inline_pulse(Pulse.Lib.Reference.pts_to $(q) #1.0R $(v)))
_preserves(_inline_pulse(Pulse.Lib.Reference.pts_to $(r) #1.0R $(w)))
int32_t impl_two(_plain int32_t *q, _plain int32_t *r) { return 0; }

/* Both kinds of witness component at once: `a` and `b` are bare (owned)
   pointers, so each contributes an *elim* component, while `v` and `w` are
   ghosts. The witness is therefore nested on both sides,

     c = ((ty_int32_t & ty_int32_t) & (ty_int32_t & ty_int32_t))

   and the wrapper projects all four bindings at depth 2. */
_ghost_arg(int32_t v)
_ghost_arg(int32_t w)
_requires(*a > 0 && *a < 100 && *b > 0 && *b < 100)
_preserves(_inline_pulse(Pulse.Lib.Reference.pts_to $(q) #1.0R $(v)))
_preserves(_inline_pulse(Pulse.Lib.Reference.pts_to $(r) #1.0R $(w)))
int32_t impl_mixed(int32_t *a, int32_t *b, _plain int32_t *q, _plain int32_t *r)
{
    return *a + *b;
}

/* Control for the case above with the ghosts removed: two elim components and
   no ghost pair, so `c = (ty_int32_t & ty_int32_t)`. If both this and
   `impl_mixed` fail, the cause is multi-component elim witnesses at an
   indirect call site rather than anything to do with ghost arguments. */
_requires(*a > 0 && *a < 100 && *b > 0 && *b < 100)
int32_t impl_elim_two(int32_t *a, int32_t *b)
{
    return *a + *b;
}

/* Same C signature as `impl_elim_two`, but both parameters are `_plain`, so
   this one's witness is empty (`c = unit`) where `impl_elim_two`'s carries
   both pointees (`c = (ty_int32_t & ty_int32_t)`). Nothing else distinguishes
   them, so a variable holding either has the same C type. */
_ensures(return == 0)
int32_t impl_plain_two(_plain int32_t *a, _plain int32_t *b)
{
    return 0;
}

/* A *weaker* contract for `impl_mixed`, advertised by the `m` field of
   `struct ops` below.

   `weaken` moves `is_valid` from `(pre, post)` to `(pre_w, post_w)` given
   ghost coercions `pre_w ==> pre` and `post ==> post_w`. A *stronger* pre
   therefore makes `is_valid f div pre_w post_w` a *weaker* claim about `f` --
   one `of_fn_div_valid` cannot produce, so `weaken` is the only route to it.
   Here `pre_w` additionally pins the two ghost components of the witness, so
   the field advertises a contract usable only at `q = 0`, `r = 1`.

   `pre_w` is built by *applying* `pre_of` rather than by restating the emitted
   slprop, so it tracks whatever PAL emits. The two conditions are separate
   `pure` conjuncts joined by `**`: Pulse never splits a conjunctive
   `pure (p /\ q)`, so writing them together would make them useless for
   matching -- and matching them is what pins the call site's ghost holes.

   `pre_w` is `pulse_eager_unfold`, like `pre_of` itself: a plain `let` would
   be opaque to the slprop matcher and the ghost holes at the indirect call
   site would stay unsolved. The post is not weakened at all, so `post_of` is
   passed through directly and `m_wpost` is an identity coercion -- it still
   has to exist, since `weaken` demands one. It needs `prevent_lifting` because
   `post_of` has a top-level `exists*`, which Pulse would otherwise eliminate
   into hidden implicit binders, changing the coercion's type (Error 189). */
_include_pulse(Ops_spec,
  let m_dom : Type0 =
    ((ref Typedef_int32_t.ty_int32_t) & (ref Typedef_int32_t.ty_int32_t) &
     (ref Typedef_int32_t.ty_int32_t) & (ref Typedef_int32_t.ty_int32_t))

  let m_wit : Type0 =
    ((Typedef_int32_t.ty_int32_t & Typedef_int32_t.ty_int32_t) &
     (Typedef_int32_t.ty_int32_t & Typedef_int32_t.ty_int32_t))

  [@@pulse_eager_unfold]
  unfold let m_pre_w (x: m_dom) (y: erased m_wit) : slprop =
    Pulse.Lib.C.FuncPtr.pre_of Funcptr_impl_mixed.func_impl_mixed__fp x y **
    pure (fst (snd (reveal y)) == 0l) **
    pure (snd (snd (reveal y)) == 1l)

  ghost fn m_wpre (x: m_dom) (y: erased m_wit)
    requires m_pre_w x y
    ensures Pulse.Lib.C.FuncPtr.pre_of Funcptr_impl_mixed.func_impl_mixed__fp x y
  {
    drop_ (pure (fst (snd (reveal y)) == 0l));
    drop_ (pure (snd (snd (reveal y)) == 1l));
  }

  ghost fn m_wpost (x: m_dom) (y: erased m_wit) (r: Typedef_int32_t.ty_int32_t)
    requires Pulse.Lib.C.FuncPtr.prevent_lifting
               (Pulse.Lib.C.FuncPtr.post_of Funcptr_impl_mixed.func_impl_mixed__fp x y r)
    ensures Pulse.Lib.C.FuncPtr.post_of Funcptr_impl_mixed.func_impl_mixed__fp x y r
  {
    ()
  }
)

/* The `m` field carries the weakened contract as a field-level `_refine`, so
   any owner of a `struct ops` value may call through `m` without first
   re-deriving validity from `impl_mixed`. */
struct ops {
    _ghost_arg(int32_t v)
    int32_t (*f)(_plain int32_t *q);
    _ghost_arg(int32_t v)
    _ghost_arg(int32_t w)
    int32_t (*g)(_plain int32_t *q, _plain int32_t *r);
    _ghost_arg(int32_t v)
    _ghost_arg(int32_t w)
    _refine((_slprop) _inline_pulse(
        Pulse.Lib.C.FuncPtr.is_valid $(this) true Ops_spec.m_pre_w
          (Pulse.Lib.C.FuncPtr.post_of Funcptr_impl_mixed.func_impl_mixed__fp)))
    int32_t (*m)(int32_t *a, int32_t *b, _plain int32_t *q, _plain int32_t *r);
    int32_t (*e)(int32_t *a, int32_t *b);
};

static const struct ops o = {
    .f = impl_one, .g = impl_two, .m = impl_mixed, .e = impl_elim_two
};

/* A direct call, for contrast: the ghost arguments are ordinary implicits and
   any number of them is already fine. (test/ghost_arg declares ghost-arg
   functions but never calls one, so this is the only direct-call coverage.) */
_preserves(_inline_pulse(Pulse.Lib.Reference.pts_to $(q) #1.0R 0l))
_preserves(_inline_pulse(Pulse.Lib.Reference.pts_to $(r) #1.0R 1l))
_requires(*a > 0 && *a < 100 && *b > 0 && *b < 100)
int32_t call_direct_mixed(int32_t *a, int32_t *b,
                          _plain int32_t *q, _plain int32_t *r)
{
    return impl_mixed(a, b, q, r);
}

/* The same calls through the function pointers in `o`. Same shape as
   `call_via_addr_of_global_struct` in test/addr_global; the only difference is
   the `_ghost_arg` on the callees. */
_preserves(_inline_pulse(Pulse.Lib.Reference.pts_to $(q) #1.0R 0l))
int32_t call_via_o_one(_plain int32_t *q)
{
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_impl_one.func_impl_one__fp);
    _ghost_stmt(Global_o.acquire_var_o ());
    const struct ops *p = &o;
    return p->f(q);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
    _ghost_stmt(drop_ (exists* fr. pts_to Global_o.addr_var_o #fr _));
}

_preserves(_inline_pulse(Pulse.Lib.Reference.pts_to $(q) #1.0R 0l))
_preserves(_inline_pulse(Pulse.Lib.Reference.pts_to $(r) #1.0R 1l))
int32_t call_via_o_two(_plain int32_t *q, _plain int32_t *r)
{
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_impl_two.func_impl_two__fp);
    _ghost_stmt(Global_o.acquire_var_o ());
    const struct ops *p = &o;
    return p->g(q, r);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
    _ghost_stmt(drop_ (exists* fr. pts_to Global_o.addr_var_o #fr _));
}

/* The mixed case through the pointer: `hide ((!a, !b), (_, _))`. */
_preserves(_inline_pulse(Pulse.Lib.Reference.pts_to $(q) #1.0R 0l))
_preserves(_inline_pulse(Pulse.Lib.Reference.pts_to $(r) #1.0R 1l))
_requires(*a > 0 && *a < 100 && *b > 0 && *b < 100)
int32_t call_via_o_mixed(int32_t *a, int32_t *b,
                         _plain int32_t *q, _plain int32_t *r)
{
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_impl_mixed.func_impl_mixed__fp);
    _ghost_stmt(Global_o.acquire_var_o ());
    const struct ops *p = &o;
    return p->m(a, b, q, r);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
    _ghost_stmt(drop_ (exists* fr. pts_to Global_o.addr_var_o #fr _));
}

/* Control: the same two owned pointers with no ghost arguments. */
_requires(*a > 0 && *a < 100 && *b > 0 && *b < 100)
int32_t call_via_o_elim_two(int32_t *a, int32_t *b)
{
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_impl_elim_two.func_impl_elim_two__fp);
    _ghost_stmt(Global_o.acquire_var_o ());
    const struct ops *p = &o;
    return p->e(a, b);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
    _ghost_stmt(drop_ (exists* fr. pts_to Global_o.addr_var_o #fr _));
}

/* One variable, both shapes written into it. Assignment is witness-agnostic:
   `func_ptr` is indexed by argument and return type only, so both `of_fn_div`
   results have the same type regardless of what each callee's witness is. */
void assign_across_shapes(void)
{
    int32_t (*fp)(int32_t *, int32_t *);
    fp = impl_elim_two;
    fp = impl_plain_two;
    fp = impl_elim_two;
}

/* The same variable, called after each write. `impl_elim_two` needs a
   two-component witness and `impl_plain_two` needs none, so no single declared
   type can describe both -- which is the point. Each call's `pre`, `post` and
   witness are pinned by the `is_valid` in scope, and PAL already emits `_` for
   `pre` and `post`; only the witness is still read off the declaration. */
_requires(*a > 0 && *a < 100 && *b > 0 && *b < 100)
int32_t call_across_shapes(int32_t *a, int32_t *b)
{
    int32_t (*fp)(int32_t *, int32_t *);

    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_impl_elim_two.func_impl_elim_two__fp);
    fp = impl_elim_two;
    int32_t r1 = fp(a, b);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);

    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_impl_plain_two.func_impl_plain_two__fp);
    fp = impl_plain_two;
    int32_t r2 = fp(a, b);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);

    return r1 + r2;
}

/* The same mixed callee through a *local* function pointer rather than a
   struct field. The local carries NO `_ghost_arg`s: the witness is inferred at
   the call site, so the declared type does not have to describe the callee's
   ghost arity. No global is involved, so unlike the `o` cases there is nothing
   to acquire or drop besides the validity fact. */
_requires(*a > 0 && *a < 100 && *b > 0 && *b < 100)
_preserves(_inline_pulse(Pulse.Lib.Reference.pts_to $(q) #1.0R 0l))
_preserves(_inline_pulse(Pulse.Lib.Reference.pts_to $(r) #1.0R 1l))
int32_t call_via_local_fp(int32_t *a, int32_t *b,
                          _plain int32_t *q, _plain int32_t *r)
{
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_impl_mixed.func_impl_mixed__fp);
    int32_t (*fp)(int32_t *, int32_t *, _plain int32_t *, _plain int32_t *) = impl_mixed;
    return fp(a, b, q, r);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* ---------------------------------------------------------------------------
   Handing out a `struct ops *` whose `m` field is already known valid.

   No typedef and no hand-written `_ensures`: PAL's default ownership for a
   returned `struct ops *` already includes `struct_ops__pred`, which is
   exactly where the field refinement landed. -------------------------------*/

/* This is where `weaken` earns its place. `of_fn_div_valid` yields validity at
   `impl_mixed`'s *own* contract; the `m` field advertises the strictly weaker
   one, and the only route from the former to the latter is `weaken` with the
   two ghost coercions.

   `weaken`'s `pre`/`post` are written out rather than left as holes: F* checks
   arguments left to right, so leaving them uninstantiated makes the two
   coercions' types unresolvable (Error 189). */
_allocated
struct ops *get_ops(void)
{
    struct ops *p = (struct ops *) malloc(sizeof(struct ops));
    *p = (struct ops){
        .f = impl_one, .g = impl_two, .m = impl_mixed, .e = impl_elim_two
    };
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_impl_mixed.func_impl_mixed__fp);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.weaken _ true true
                    (Pulse.Lib.C.FuncPtr.pre_of Funcptr_impl_mixed.func_impl_mixed__fp)
                    (Pulse.Lib.C.FuncPtr.post_of Funcptr_impl_mixed.func_impl_mixed__fp)
                    Ops_spec.m_pre_w
                    (Pulse.Lib.C.FuncPtr.post_of Funcptr_impl_mixed.func_impl_mixed__fp)
                    Ops_spec.m_wpre Ops_spec.m_wpost);
    return p;
}

/* Calling `m` through the returned pointer. Note the absence of any
   `of_fn_div_valid`: validity travels with the pointer, through the field
   refinement folded into `struct_ops__pred`. That absence is what this
   function asserts. */
_requires(*a > 0 && *a < 100 && *b > 0 && *b < 100)
_preserves(_inline_pulse(Pulse.Lib.Reference.pts_to $(q) #1.0R 0l))
_preserves(_inline_pulse(Pulse.Lib.Reference.pts_to $(r) #1.0R 1l))
int32_t call_via_returned_ops(int32_t *a, int32_t *b,
                              _plain int32_t *q, _plain int32_t *r)
{
    struct ops *p = get_ops();
    int32_t res = p->m(a, b, q, r);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
    free(p);
    return res;
}
