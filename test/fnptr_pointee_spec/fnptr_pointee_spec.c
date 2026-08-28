#include "pal.h"
#include <stdint.h>

/* FAILS. Postconditions about a pointee do not survive an indirect call --
   https://github.com/FStarLang/pal/issues/279.

   The `__fp` wrapper states its pure postcondition as `PRE ==> POST`, reusing
   the same `req_conj` it emitted for the `requires`. In the `ensures` that
   `PRE` is read in the *post* state, so for a callee that mutates a pointee it
   mentions, the implication is a tautology and carries nothing.

   The issue records the two halves as separate defects. On this branch only
   the first still behaves as filed; see `call_indirect_old`. The last case,
   `call_indirect_deep`, is a third symptom the issue does not mention: for a
   double pointer the *precondition* breaks too. */

/* The guard alone is enough to lose the postcondition -- nothing here is
   relational and there is no `_old`.

   The wrapper's `requires` binds the pointee from the witness as `val_p_0`,
   and its `ensures` introduces a *fresh* `exists* (val_p_0: ..)`, so the copy
   of `PRE` is captured by the post-state binder:

     ensures (exists* (val_p_0: ty_int32_t).
       pts_to var_p #1.0R val_p_0 ** ty_int32_t__pred val_p_0 1.0R **
       pure ((v val_p_0 < 100) ==> (v (!var_p) < 101)))

   Both sides now denote the post value, so the conjunct says
   `(x < 100) ==> (x < 101)`. (Filed against a9ebbed, where the same collapse
   happened by re-reading `(!var_p)` on both sides rather than by capture.)

     * Error 19 at out/Func_call_indirect_norel.fst(28,2-28,41):
       - Failed to prove pure property: 'v _val_p_015 < 101' */
void inc2(int32_t *p) _requires(*p < 100) _ensures(*p < 101) { *p = *p + 1; }

_requires(*q < 100)
_ensures(*q < 101)
void call_indirect_norel(int32_t *q)
{
  void (*f)(int32_t *) = inc2;
  _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_inc2.func_inc2__fp);
  f(q);
  _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* The relational case, and it no longer matches the issue. #279 reports that
   `old (...)` is emitted with no binder in scope, so the wrapper is vacuous
   and silently accepts even a false `_old` contract. That is no longer true:
   the wrapper does not typecheck at all.

   `old (!var_p)` sends Pulse looking for the *pre*-state `pts_to`, which is
   under the witness's pattern `let` -- the binding form the call site's
   inference depends on -- and Pulse does not elaborate `!` into a match
   branch:

     * Error 228 at out/Funcptr_inc.fsti(24,40-24,48):
       - Cannot prove:  Pulse.Lib.Reference.pts_to x_fp (*?u332*)_
       - In the context:
           let w_fp_e, _ = y_fp in
           (Pulse.Lib.Reference.pts_to x_fp w_fp_e ** ...

   So `_old` on an address-taken function is now a hard failure rather than a
   silent one, and `Func_call_indirect_old` below is never reached. `Func_inc`
   itself verifies: the contract is true of the body, and a direct call
   propagates it. */
void inc(int32_t *p) _requires(*p < 100) _ensures(*p == _old(*p) + 1) { *p = *p + 1; }

_requires(*q < 100)
_ensures(*q == _old(*q) + 1)
void call_indirect_old(int32_t *q)
{
  void (*f)(int32_t *) = inc;
  _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_inc.func_inc__fp);
  f(q);
  _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* Every witness feature at once, plus two mutated pointees.

   `d` contributes two elim leaves (its value and `struct_dep__spec`, since the
   `y` field is a pointer), so `a`'s pre-state value sits at elim index 2 and
   `b`'s at 3 -- the post has to project each one out at its own offset, not at
   0. The two `_old`s appear together in one conjunct, `q` is `_plain` (so it
   is `preserves`d and takes no elim leaf), and the `_ghost_arg` fills the
   ghost half. The body updates `*b` before `*a`, so reading either `_old` in
   the post state gives the wrong answer rather than a vacuous one. */
struct dep {
  int32_t x;
  int32_t *y;
};

_ghost_arg(int32_t v)
_requires(*a > 0 && *a < 100 && *b > 0 && *b < 100)
_ensures(*a == _old(*a) + 1 && *b == _old(*b) + _old(*a))
_preserves(_inline_pulse(Pulse.Lib.Reference.pts_to $(q) #1.0R $(v)))
int32_t impl_mixed(struct dep *d, int32_t *a, int32_t *b, _plain int32_t *q)
{
  *b = *b + *a;
  *a = *a + 1;
  return *a;
}

/* The `m` field carries `is_valid` as a field-level `_refine`; reaching it
   through a `const` global loses that (the global's `acquire` yields a bare
   `pts_to`, not the struct's `__pred`), so `of_fn_div_valid` reintroduces it
   for free -- see `test/fnptr_spec/fnptr_spec.c`. */
struct ops_mixed {
  _refine((_slprop) _inline_pulse(
      Pulse.Lib.C.FuncPtr.is_valid $(this) true
        (Pulse.Lib.C.FuncPtr.pre_of Funcptr_impl_mixed.func_impl_mixed__fp)
        (Pulse.Lib.C.FuncPtr.post_of Funcptr_impl_mixed.func_impl_mixed__fp)))
  int32_t (*m)(struct dep *d, int32_t *a, int32_t *b, _plain int32_t *q);
};

static const struct ops_mixed o_m = {.m = impl_mixed};

_ghost_arg(int32_t v)
_requires(*a > 0 && *a < 100 && *b > 0 && *b < 100)
_ensures(*a == _old(*a) + 1 && *b == _old(*b) + _old(*a))
_preserves(_inline_pulse(Pulse.Lib.Reference.pts_to $(q) #1.0R $(v)))
int32_t call_mixed(struct dep *d, int32_t *a, int32_t *b, _plain int32_t *q)
{
  _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_impl_mixed.func_impl_mixed__fp);
  _ghost_stmt(Global_o_m.acquire_var_o_m ());
  const struct ops_mixed *p = &o_m;
  return p->m(d, a, b, q);
  _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
  _ghost_stmt(drop_ (exists* fr. pts_to Global_o_m.addr_var_o_m #fr _));
}

/* A pointee reached through *two* derefs. `bump` on its own verifies: a normal
   function states `**p` as `!(!var_p)` and `_old(**p)` as `old (!(!var_p))`,
   both fine. Address-taking it breaks the precondition as well as the post,
   because only the innermost `*p` is rewritten to a witness binding:

     * Error 12 at out/Funcptr_bump.fsti(17,37-17,47):
       - Expected type FStar.Int32.t but !val_p_0 has type
           fn requires val_p_0 |-> Pulse.Class.PtsTo.Frac _ _ ...

   `**p` comes out as `!val_p_0`, and the `requires` sits under the witness's
   pattern `let` where Pulse will not elaborate `!`, so the read stays a `fn`
   instead of a value. The witness already carries the leaf (`val_p_1`); the
   spec just does not name it. */
void bump(int32_t **p) _requires(**p < 100) _ensures(**p == _old(**p) + 1) { **p = **p + 1; }

_requires(**q < 100)
_ensures(**q == _old(**q) + 1)
void call_indirect_deep(int32_t **q)
{
  void (*f)(int32_t **) = bump;
  _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_bump.func_bump__fp);
  f(q);
  _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}
