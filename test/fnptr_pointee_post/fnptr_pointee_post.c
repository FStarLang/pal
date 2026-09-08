#include "pal.h"
#include <stdint.h>

/* Postconditions about a *pointee* are lost across an indirect call.
   https://github.com/FStarLang/pal/issues/279

   THIS DIRECTORY IS EXPECTED TO FAIL. Every function below states a contract
   that is TRUE OF ITS BODY, and the direct-call controls prove it. They are
   red only because the `__fp` wrapper drops the contract, so this suite
   returning to green is the acceptance test for the fix.

   The defect is that the wrapper's `ensures` has no name for the PRE-state
   value. Two symptoms, one cause:

     1. The post's pure part is emitted as `PRE ==> POST`, but `PRE` is
        re-read in the post-state, where `*p` denotes the value AFTER the
        call. For a callee that mutates `*p` the conjunct degenerates to
        `x < 100 ==> x < 101`, a tautology carrying no information. This costs
        every pointee postcondition, relational or not.

     2. `_old(*p)` emits a bare `old`, which Pulse resolves against an
        `exists*` binder in the requires. The wrapper has none: its requires
        binds the witness by pattern-`let`, and its ensures introduces a
        *fresh* existential. The `old (...)` term refers to nothing.

   The pre-state values do exist -- the wrapper's witness `y_fp` carries them
   in its ELIMS half and is a `fn` parameter, hence in scope in the ensures
   too. The post simply never binds them. So the fix is to bind the ELIMS half
   in the post (as the ghost bindings already are) and point both `PRE` and
   `old` at it.

   Note this makes stale the comment in src/pass/emit.rs attributing the `_old`
   limitation to the FuncPtr contract `pre: a->slprop`, `post: a->b->slprop`
   being non-relational. That was true when the witness carried nothing
   useful; the `(ELIMS & GHOSTS)` witness changed it.

   ---------------------------------------------------------------------------
   No false-contract case.

   The issue's section 2 demonstrates the unbound `old` with a contract that is
   FALSE of its body -- `_ensures(*p == _old(*p) + 2)` over a body that adds 1
   -- and reports that the wrapper accepts it while the direct function
   rejects it. That case is deliberately NOT reproduced here:

     * It could never pass. The contract really is false, so the direct module
       correctly errors forever, fix or no fix, and this tree has no
       expected-failure convention with which to say so.

     * It no longer reproduces. Measured on this branch, the wrapper gives
       Error 228 at the `old (!var_p)` column rather than the issue's
       "Verified module". The silent acceptance it existed to document is
       already gone -- though the contract is still not CHECKED; it now fails
       for an incidental reason at a confusing location.
   ---------------------------------------------------------------------------
   MEASURED (F* nightly-2026-09-04, branch heili/fnptr-pointee-postcond).
   3 errors; 4 further modules are dependency-blocked and never run, so the
   error count understates the damage.

     case  module                     result
     ----  -------------------------  ---------------------------------------
     F1    Func_inc_direct            Verified
     F1    Func_call_direct           Verified   <- direct route keeps `_old`
     F2    Func_add / Funcptr_add     Verified
     F2    Func_call_add              Verified
     F3    Func_peek / Funcptr_peek   Verified
     F3    Func_call_peek             Verified   <- owned ptr arg is fine
     A     Func_inc2                  Verified
     A     Funcptr_inc2               Verified   <- vacuously; post is a tautology
     A     Func_call_indirect_norel   Error 19
     C     Func_inc                   Verified
     C     Funcptr_inc                Error 228
     C     Func_call_indirect_old     blocked by Funcptr_inc
     D     Func_apply_inc             blocked by Funcptr_inc
     G     Func_impl_kitchen          Verified
     G     Funcptr_impl_kitchen       Error 228
     G     Func_call_kitchen          blocked by Funcptr_impl_kitchen
     G     Global_o                   blocked by Funcptr_impl_kitchen

   A -- Error 19 at out/Func_call_indirect_norel.fst(28,2-28,41):
          Failed to prove pure property: `v _val_p_015 < 101`
        Note the wrapper itself VERIFIES. Its ensures is

          pure ((Int32.v (!var_p) < 100) ==> (Int32.v (!var_p) < 101))

        with both occurrences denoting the POST state -- true, and empty. The
        loss only becomes visible at the caller.

   C -- Error 228 at out/Funcptr_inc.fsti(23,40-23,48), the `old (!var_p)`
        column of

          pure ((Int32.v (!var_p) < 100) ==>
                (Int32.v (!var_p) = Int32.v (old (!var_p)) + 1))

          Cannot prove:   pts_to x_fp (*?u380*)_
          In the context: let val_p_0, _ = y_fp in
                          pts_to x_fp val_p_0 ** pure (v val_p_0 < 100)

        The context is the diagnosis: the pre-state value `val_p_0` is sitting
        in the witness, and `old` is hunting for a `pts_to` to resolve against
        in a post-state that has only a fresh existential.

   G -- Error 228 at out/Funcptr_impl_kitchen.fsti(43,40-43,48), the same
        `old` column, with the same shape:

          Cannot prove:   pts_to x_fp._1 (*?u1529*)_
          In the context: let (val_a_0, (val_d_0, val_d_1)), var_v = y_fp in
                          pts_to x_fp._1 val_a_0 **
                          pts_to x_fp._3 val_d_0 **
                          Struct_dep.struct_dep__pred val_d_0 1.0R val_d_1 **
                          with_pure (0 < v val_d_0.struct_dep__x)
                            (fun _ -> pts_to x_fp._2 var_v **
                                      pure (0 < v val_a_0 && v val_a_0 < 100))

        This is the answer to the question G was written to ask: the features
        do NOT interact badly. The combined witness is exactly the predicted
        ((ty_int32_t & (struct_dep & struct_dep__spec)) & ty_int32_t) -- the
        `__spec` component `val_d_1`, the struct refinement (`with_pure`), the
        ghost `var_v` and the two elims are all present and correct. G fails
        at the identical column offset as the minimal case C, and for the
        identical reason. #279 is orthogonal to the rest of the machinery.
   --------------------------------------------------------------------------- */

/* ==========================================================================
   F. Controls. These must VERIFY. If one of them goes red the rest of the
   file proves nothing, because the failure would not be specific to
   postconditions about pointees.
   ========================================================================== */

/* F1. A pointee postcondition, relational, on a function whose address is NOT
   taken. No wrapper is generated, `old` binds to the requires' existential,
   and the contract propagates to a direct caller. This is the behaviour the
   indirect cases below fail to reproduce. */
void inc_direct(int32_t *p)
    _requires(*p < 100)
    _ensures(*p == _old(*p) + 1)
{
    *p = *p + 1;
}

_requires(*q < 100)
_ensures(*q == _old(*q) + 1)
void call_direct(int32_t *q)
{
    inc_direct(q);
}

/* F2. Address-taken and called indirectly, but the postcondition constrains
   only the RETURN VALUE and the precondition mentions only scalars. This is
   the shape every enabled test in test/func_pointer uses, and it is
   unaffected: `PRE ==> POST` is correct precisely when `PRE` mentions no
   mutable pointee, since then re-reading it in the post-state is harmless. */
_requires(x > 0 && x < 100 && y > 0 && y < 100)
_ensures(return == x + y)
int32_t add(int32_t x, int32_t y)
{
    return x + y;
}

_ensures(return == 5)
int32_t call_add(void)
{
    int32_t (*f)(int32_t, int32_t) = add;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
    return f(2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* F3. Address-taken with an OWNED pointer argument, so the wrapper's witness
   has a real elims component -- but with no precondition and no
   postcondition about the pointee. Isolates the two variables: owned pointer
   arguments are threaded correctly, and it is specifically a contract ABOUT
   the pointee that is dropped. */
_ensures(return == 7)
int32_t peek(int32_t *p)
{
    return 7;
}

_ensures(return == 7)
int32_t call_peek(int32_t *p)
{
    int32_t (*f)(int32_t *) = peek;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_peek.func_peek__fp);
    return f(p);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* ==========================================================================
   A. Issue section 1 -- a NON-RELATIONAL pointee postcondition is lost.

   No `_old` anywhere, so this is not about relational specs. `inc2` really
   does establish `*p < 101`, and `Func_inc2` verifies. The wrapper's post
   reduces to the tautology `(!var_p < 100) ==> (!var_p < 101)`, both
   occurrences denoting the post-state, so the caller learns nothing.
   ========================================================================== */

void inc2(int32_t *p)
    _requires(*p < 100)
    _ensures(*p < 101)
{
    *p = *p + 1;
}

_requires(*q < 100)
_ensures(*q < 101)
void call_indirect_norel(int32_t *q)
{
    void (*f)(int32_t *) = inc2;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_inc2.func_inc2__fp);
    f(q);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* ==========================================================================
   C. Issue section 2 -- a RELATIONAL `_old` postcondition, through a local
   function pointer. The contract is true of the body (F1 proves it via the
   direct route); only the indirect path loses it.
   ========================================================================== */

void inc(int32_t *p)
    _requires(*p < 100)
    _ensures(*p == _old(*p) + 1)
{
    *p = *p + 1;
}

_requires(*q < 100)
_ensures(*q == _old(*q) + 1)
void call_indirect_old(int32_t *q)
{
    void (*f)(int32_t *) = inc;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_inc.func_inc__fp);
    f(q);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* ==========================================================================
   D. The same defect via the callback-PARAMETER route, where validity arrives
   as a `_refine` on the parameter rather than from `of_fn_div_valid` on a
   local. Confirms the loss is in the wrapper's spec itself, not in one
   particular way of reaching it.
   ========================================================================== */

_requires(*p < 100)
_ensures(*p == _old(*p) + 1)
void apply_inc(void (*op)(int32_t *)
                   _refine((_slprop) _inline_pulse(
                       Pulse.Lib.C.FuncPtr.is_valid $(this) true
                           (Pulse.Lib.C.FuncPtr.pre_of Funcptr_inc.func_inc__fp)
                           (Pulse.Lib.C.FuncPtr.post_of Funcptr_inc.func_inc__fp))),
               int32_t *p)
{
    op(p);
}

/* ==========================================================================
   G. Everything at once.

   One callee combining every function-pointer feature this branch supports
   with the postcondition that #279 drops:

     * `_ghost_arg(int32_t v)`               -- the GHOSTS half of the witness
     * `int32_t *a`, owned                   -- an ELIMS component
     * `struct dep *d`, owned, with a        -- a SECOND elims component, since
       pointer field and a `_refine`            `y` gives `dep` a `__spec`
                                                companion (the shape of #277)
     * `_plain int32_t *q` tied to the ghost -- pins `v` at the call site
     * `_ensures(*a == _old(*a) + 1)`        -- the pointee postcondition (#279)

   reached through a global `struct ops`. The witness is nested on both sides,

     c = ((ty_int32_t & (struct_dep & struct_dep__spec)) & ty_int32_t)

   and the post has to bind the `ty_int32_t` at elims-position 0 to express
   `_old(*a)`.

   This is the case that matters most for the eventual fix: it is where the
   `(ELIMS & GHOSTS)` witness, the `__spec` component, the struct refinement,
   the ghost argument and the pre-state binding all have to coexist. The
   measurement of interest is whether it fails ONLY on the #279 postcondition,
   or whether the features interact and produce something worse.
   ========================================================================== */

/* The pointer field gives `dep` a `__spec` companion; the refinement rides
   along in `struct_dep__pred`. */
struct _refine(this.x > 0) dep {
    int32_t x;
    int32_t *y;
};

_ghost_arg(int32_t v)
_requires(*a > 0 && *a < 100)
_preserves(_inline_pulse(Pulse.Lib.Reference.pts_to $(q) #1.0R $(v)))
_ensures(*a == _old(*a) + 1)
int32_t impl_kitchen(int32_t *a, _plain int32_t *q, struct dep *d)
{
    *a = *a + 1;
    return d->x;
}

struct ops {
    int32_t (*k)(int32_t *a, _plain int32_t *q, struct dep *d);
};

static const struct ops o = {.k = impl_kitchen};

/* Validity comes from `of_fn_div_valid`, so the field carries no `_refine`
   and needs no weakened contract: the ghost `v` is pinned by matching this
   caller's `_preserves` against the callee's. The declared type of `k` says
   nothing about ghost arity -- the witness is inferred at the call site. */
_ghost_arg(int32_t v)
_requires(*a > 0 && *a < 100)
_preserves(_inline_pulse(Pulse.Lib.Reference.pts_to $(q) #1.0R $(v)))
_ensures(*a == _old(*a) + 1)
int32_t call_kitchen(int32_t *a, _plain int32_t *q, struct dep *d)
{
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_impl_kitchen.func_impl_kitchen__fp);
    _ghost_stmt(Global_o.acquire_var_o ());
    const struct ops *p = &o;
    return p->k(a, q, d);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
    _ghost_stmt(drop_ (exists* fr. pts_to Global_o.addr_var_o #fr _));
}
