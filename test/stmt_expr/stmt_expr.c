#include "pal.h"
#include <stdint.h>

/*
 * GNU statement expressions, `({ ... })`.
 *
 * Two positions, with two different rules.
 *
 * In STATEMENT position the value is discarded, so `({ s1; s2; e; });` is
 * exactly `{ s1; s2; e; }` and no restriction on the body is needed.  This is
 * where the idiom mostly appears in FunOS: do-something-and-check macros
 * expanded for their effect, such as UNIMPLEMENTED().
 *
 * In RVALUE position the body must reduce to a single expression, because an
 * rvalue has nowhere to put the preceding statements and hoisting them out
 * would move them across the surrounding expression's other operands -- which
 * C's sequencing rules do not permit in general.  Statements are skipped
 * ahead of the final expression only when they cannot affect it: a null
 * statement, and a declaration group of nothing but static assertions.  FunOS
 * reaches the latter through call_fn_on_stack, whose expansion is a macro
 * argument type check followed by the call.
 *
 * FALSIFICATION (run by hand; not included, because this suite must pass):
 *
 *   1. Delete the trStmt arm.  `discarded_value` and `effect_in_statement_
 *      position` become admit()s.
 *
 *   2. Delete the trRValue arm.  Every other function here becomes an
 *      admit().
 *
 *   3. Delete the hoisting branch of the trRValue arm (the one guarded by
 *      hoistTarget).  `hoisted_*` below become admit()s.
 *
 *   4. Remove the NoHoist guards from ?: and from && / ||, then change
 *      `not_hoisted_out_of_short_circuit` and
 *      `not_hoisted_out_of_conditional` to bodies that declare a local -- so
 *      they must hoist rather than reduce.  Their _ensures then fail, because
 *      the statements run on a path C does not run them on.
 */

/* ------------------------------------------------------------------ */
/* rvalue position                                                     */

#define DOUBLE(x) ({ (x) * 2; })

uint32_t through_a_single_expression(uint32_t n)
	_requires(n < 100)
	_ensures(return == n * 2)
{
	return DOUBLE(n);
}

/* A null statement ahead of the value: skipped, since it does nothing. */
uint32_t leading_null_statement(uint32_t n)
	_requires(n < 100)
	_ensures(return == n + 1)
{
	return ({
		;
		n + 1;
	});
}

/*
 * The call_fn_on_stack shape: a static assertion about the macro's argument,
 * then the expression.  A static assertion has already been checked by the
 * compiler and contributes nothing at run time.
 */
#define CHECKED_ADD(a, b)                                                      \
	({                                                                     \
		_Static_assert(sizeof(a) == sizeof(b), "size mismatch");        \
		(a) + (b);                                                     \
	})

uint32_t leading_static_assert(uint32_t a, uint32_t b)
	_requires(a < 100 && b < 100)
	_ensures(return == a + b)
{
	return CHECKED_ADD(a, b);
}

/* Nested, and in argument position rather than return position. */
uint32_t nested(uint32_t n)
	_requires(n < 100)
	_ensures(return == n * 4)
{
	return DOUBLE(({ n * 2; }));
}

/* ------------------------------------------------------------------ */
/* statement position: no restriction on the body                      */

/*
 * Several statements, and a value that is thrown away.  If the arm translated
 * only the last statement, or only the value, the writes below would be lost
 * and the _ensures would fail.
 */
uint32_t effect_in_statement_position(uint32_t n)
	_requires(n < 100)
	_ensures(return == n + 3)
{
	uint32_t acc = n;
	({
		acc = acc + 1;
		acc = acc + 1;
		acc + 1;
	});
	return acc + 1;
}

void discarded_value(uint32_t *p)
	_requires(*p < 100)
	_ensures(*p == _old(*p) + 1)
{
	({
		*p = *p + 1;
		*p;
	});
}

/* ------------------------------------------------------------------ */

/*
 * NOT reducible: the body declares a variable, so the trRValue arm refuses it
 * and reports "unsupported rvalue expression StmtExpr".  The refusal is
 * deliberate -- translating this as `1` would silently drop the write to *p --
 * and it is recorded here rather than compiled, because the emitted admit()
 * does not typecheck in return position and this suite must pass:
 *
 *	uint32_t not_reducible(uint32_t *p)
 *	{
 *		return ({
 *			uint32_t tmp = *p;
 *			*p = tmp;
 *			1;
 *		});
 *	}
 *
 * A future relaxation of the rule has to confront this case.
 */

/* ------------------------------------------------------------------ */
/* rvalue position, hoisted                                            */

/*
 * The shape most GNU macros actually have: a local bound to the argument so
 * it is evaluated once, a check on it, then the result.  FunOS's ROUND_UP is
 * exactly this, and so are DIV_ROUND_UP and the hw_info accessors.
 *
 * The body's statements cannot be dropped and cannot stay inside an rvalue,
 * so they are hoisted into the surrounding statement list -- but only where
 * that is sound.  A declaration's initializer qualifies: it is evaluated
 * exactly once and has no sibling operands for the statements to move across.
 */
#define ROUND_UP_U64(x, align)                                                 \
	({                                                                     \
		uint64_t _al = (align);                                        \
		((((uint64_t)(x)) + (_al - 1)) & (~(_al - 1)));                \
	})

/*
 * No postcondition: the true one, `return >= n && return < n + 64`, needs Z3
 * to reason about `logand` semantically, which is a fact about bitmask
 * arithmetic rather than about this feature, and PAL's specification language
 * has no `&` to restate the expression with.  What this case tests is that
 * the realistic macro shape translates at all.  `hoisted_local_is_bound`
 * below is the one that pins down the VALUE the hoist produces.
 */
uint64_t hoisted_into_a_declaration(uint64_t n)
	_requires(n < 1000)
{
	uint64_t r = ROUND_UP_U64(n, 64);
	return r;
}

/* The hoisted local really is bound once, and to the right value. */
uint64_t hoisted_local_is_bound(uint64_t n)
	_requires(n < 1000)
	_ensures(return == n + 7)
{
	uint64_t r = ({
		uint64_t tmp = n + 3;
		tmp + 4;
	});
	return r;
}

/* Several statements, including a write, in an initializer. */
uint64_t hoisted_with_effects(uint64_t *p)
	_requires(*p < 1000)
	_ensures(*p == _old(*p) + 1 && return == _old(*p) + 1)
{
	uint64_t r = ({
		uint64_t tmp = *p + 1;
		*p = tmp;
		tmp;
	});
	return r;
}

/*
 * NOT hoisted: `&&` evaluates its right operand only when the left one is
 * true, so running the statements unconditionally would change the program.
 * The body here reduces to a single expression, so it still translates -- by
 * the reduction rule, not by hoisting.  A hoist would be wrong even though
 * the result would be the same here, which is why the suppression is
 * structural rather than value-based.
 */
_Bool not_hoisted_out_of_short_circuit(uint64_t n)
	_requires(n < 1000)
	_ensures(return == (n > 2 && n < 10))
{
	return n > 2 && ({ n < 10; });
}

/*
 * NOT hoisted: a conditional operator's arms are evaluated conditionally, for
 * the same reason.
 */
uint64_t not_hoisted_out_of_conditional(uint64_t n)
	_requires(n < 1000)
	_ensures(return == (n > 2 ? n + 1 : n + 2))
{
	uint64_t r = n > 2 ? ({ n + 1; }) : ({ n + 2; });
	return r;
}
