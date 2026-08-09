#pragma once

#ifdef C2PULSE

// Dummy declaration for C assert() translation
static inline void __pal_c_assert(_Bool x) { (void)x; }
// Opaque function used to guard assert — Pulse verifies both branches
__attribute__((annotate("pal-pure"))) _Bool pal_c_assert_enabled(void);

#define __pal_concat_ind(x, y) x ## y
#define __pal_concat(x, y) __pal_concat_ind(x, y)
#define _include_pulse(modname, ...) [[clang::annotate("pal-includes", #modname, __capture_args(__VA_ARGS__))]] \
    void __pal_concat(__pal_include_anchor_, __COUNTER__) (void) {}

#define __capture_args(...) __COUNTER__

#define _requires(p) __attribute__((annotate("pal-requires", __capture_args(p))))
#define _ensures(p) __attribute__((annotate("pal-ensures", __capture_args(p))))
#define _refine(p) __attribute__((annotate("pal-refine", __capture_args(p))))
#define _refines(p) __attribute__((annotate("pal-refines", __capture_args(p))))
#define _refine_always(p) __attribute__((annotate("pal-refine-always", __capture_args(p))))
#define _refine_uninit(p) __attribute__((annotate("pal-refine-uninit", __capture_args(p))))
#define _refine_value(binding, pred) __attribute__((annotate("pal-refine-value", __capture_args(binding), __capture_args(pred))))
#define _invariant(p) __attribute__((annotate("pal-invariant", __capture_args(p))))
#define _do_while_first(name) __attribute__((annotate("pal-do-while-first", #name)))
#define _do_while_cond(name) __attribute__((annotate("pal-do-while-cond", #name)))

#define _assert(p) ({ __attribute__((annotate("pal-assert", __capture_args(p)))) {} })
#define _ghost_stmt(args) ({ __attribute__((annotate("pal-ghost-stmt", __capture_args(args)))) {} })
#define _ghost_arg(p) __attribute__((annotate("pal-ghost-arg", __capture_args(p))))

#define _plain __attribute__((annotate("pal-plain")))
#define _core_ref __attribute__((annotate("pal-core-ref")))
#define _nullable __attribute((annotate("pal-nullable")))
/* Translate a `const`-qualified parameter in the default mode rather than
   as a const one, so that its permission and pointee are quantified per
   call instead of becoming implicits of the signature. The reason to want
   that is `_nullable`: a const parameter's hold sits behind a null guard,
   and a call site that passes a literal null has nothing for those
   implicits to be solved against, so the call does not elaborate. Marking
   the parameter `_mutable` costs precision -- a caller no longer learns
   that the pointee came back unchanged -- and buys the null call site. */
#define _mutable __attribute((annotate("pal-mutable")))
#define _consumes __attribute__((annotate("pal-consumes")))
#define _out __attribute__((annotate("pal-out")))
#define _array __attribute((annotate("pal-array")))
#define _arrayptr __attribute((annotate("pal-arrayptr")))
#define _pure __attribute((annotate("pal-pure")))
#define _total __attribute((annotate("pal-total")))
#define _pulse_opaque_to_smt __attribute((annotate("pal-opaque-to-smt")))
#define _rec __attribute((annotate("pal-rec")))
#define _pulse_eager_unfold_predicate __attribute__((annotate("pal-eager-unfold-predicate")))
#define _pointer_view __attribute__((annotate("pal-pointer-view")))
#define _decreases(p) __attribute__((annotate("pal-decreases", __capture_args(p))))

#define _inline_pulse(args) _inline_pulse(__capture_args(args))

#define _let(sig, body) [[clang::annotate("pal-let", __capture_args(sig), __capture_args(body))]] \
    void __pal_concat(__pal_let_anchor_, __COUNTER__) (void) {}
#define _let_rec(sig, body) [[clang::annotate("pal-let-rec", __capture_args(sig), __capture_args(body))]] \
    void __pal_concat(__pal_let_rec_anchor_, __COUNTER__) (void) {}
#define _letimpure(sig, body) [[clang::annotate("pal-letimpure", __capture_args(sig), __capture_args(body))]] \
    void __pal_concat(__pal_letimpure_anchor_, __COUNTER__) (void) {}
#define _type(name, body) [[clang::annotate("pal-type", __capture_args(name), __capture_args(body))]] \
    void __pal_concat(__pal_type_anchor_, __COUNTER__) (void) {}

#else

#define _include_pulse(modname, ...)
#define _requires(p)
#define _ensures(p)
#define _refine(p)
#define _refines(p)
#define _refine_always(p)
#define _refine_uninit(p)
#define _refine_value(binding, pred)
#define _invariant(p)
#define _do_while_first(name)
#define _do_while_cond(name)

#define _assert(p)
#define _ghost_stmt(args)
#define _ghost_arg(p)

#define _plain
#define _core_ref
#define _nullable
#define _mutable
#define _consumes
#define _out
#define _array
#define _arrayptr
#define _pure
#define _total
#define _pulse_opaque_to_smt
#define _rec
#define _pulse_eager_unfold_predicate
#define _pointer_view
#define _decreases(p)

#define _let(sig, body)
#define _let_rec(sig, body)
#define _letimpure(sig, body)
#define _type(name, body)

#endif

// The standard `container_of` idiom (Linux `container_of`, MsQuic
// `CXPLAT_CONTAINING_RECORD`): recover a pointer to the enclosing `type` from a
// pointer to its `field`. This is the portable definition; under C2PULSE the
// translator pattern-matches this exact construct and lowers it to a verified
// container projection, so no PAL-specific spelling is required.
#define _container_of(ptr, type, field) \
    ((type *)((char *)(ptr) - __builtin_offsetof(type, field)))

#define _preserves(p) _requires(p) _ensures(p)
#define _allocated _refine((_slprop) _inline_pulse(freeable $(this)))

#define _same_as_old(x) ((x) == _old(x))
#define _preserves_value(x) _ensures(_same_as_old(x))

// Override C assert to translate to Pulse assertion
#ifdef C2PULSE
#undef assert
#define assert(x) __pal_c_assert(x)
#endif