#pragma once

#ifdef C2PULSE

#define __pal_concat_ind(x, y) x ## y
#define __pal_concat(x, y) __pal_concat_ind(x, y)
#define _include_pulse(modname, ...) [[clang::annotate("pal-includes", #modname, __capture_args(__VA_ARGS__))]] \
    void __pal_concat(__pal_include_anchor_, __COUNTER__) (void) {}

#define __capture_args(args) __COUNTER__

#define _requires(p) __attribute__((annotate("pal-requires", __capture_args(p))))
#define _ensures(p) __attribute__((annotate("pal-ensures", __capture_args(p))))
#define _refine(p) __attribute__((annotate("pal-refine", __capture_args(p))))
#define _invariant(p) __attribute__((annotate("pal-invariant", __capture_args(p))))

#define _assert(p) ({ __attribute__((annotate("pal-assert", __capture_args(p)))) {} })
#define _ghost_stmt(args) ({ __attribute__((annotate("pal-ghost-stmt", __capture_args(args)))) {} })

#define _plain __attribute__((annotate("pal-plain")))
#define _consumes __attribute__((annotate("pal-consumes")))
#define _array __attribute((annotate("pal-array")))
#define _pure __attribute((annotate("pal-pure")))

#define _inline_pulse(args) _inline_pulse(__capture_args(args))

#define _let(sig, body) [[clang::annotate("pal-let", __capture_args(sig), __capture_args(body))]] \
    void __pal_concat(__pal_let_anchor_, __COUNTER__) (void) {}
#define _let_rec(sig, body) [[clang::annotate("pal-let-rec", __capture_args(sig), __capture_args(body))]] \
    void __pal_concat(__pal_let_rec_anchor_, __COUNTER__) (void) {}

#else

#define _include_pulse(modname, ...)
#define _requires(p)
#define _ensures(p)
#define _refine(p)
#define _invariant(p)

#define _assert(p)
#define _ghost_stmt(args)

#define _plain
#define _consumes
#define _array
#define _pure

#define _let(sig, body)
#define _let_rec(sig, body)

#endif

#define _preserves(p) _requires(p) _ensures(p)
#define _allocated _refine((_slprop) _inline_pulse(freeable $(this)))

#define _same_as_old(x) ((x) == _old(x))
#define _preserves_value(x) _ensures(_same_as_old(x))