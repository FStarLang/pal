#include "pal.h"

/*
 * A struct with no members. Legal C as a GNU extension, and it turns up in
 * generated headers -- FunOS's CO3 tooling emits `struct co3_modules { }`.
 *
 * F* has no empty-record syntax, so emitting `noeq type t = { }` produced a
 * file that would not parse. PAL exited 0 and reported no diagnostic, so the
 * only symptom was an F* syntax error in output that looked fine.
 *
 * The record therefore carries a unit-typed placeholder, which must appear at
 * every literal site as well as in the declaration.
 */
struct empty {
};

/* Embedding one must work too: that is how the original was reached. */
struct wrapper {
	struct empty e;
	int x;
};

int get_x(struct wrapper *w) _requires(w->x == 7) _ensures(return == 7)
{
	return w->x;
}
