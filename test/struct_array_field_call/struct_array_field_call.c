/*
 * Writing a field of a struct, and passing a struct's array field to a callee.
 *
 * WHAT THIS TEST IS ABOUT
 * ----------------------
 * A struct whose fields are all values gets `__pred == emp`, tagged
 * `pulse_eager_unfold`, and writing any of its fields -- including an array
 * field, including handing that array field to a callee -- just works.
 *
 * As soon as the struct carries an UNANNOTATED pointer field, PAL generates a
 * non-trivial `__pred` that claims ownership of the POINTEE:
 *
 *     let predicate struct_s__pred ([@@@mkey] this: struct_s) (p: perm) (v: ...) =
 *       Pulse.Lib.Reference.pts_to (this).struct_s__q #p v.struct_s__spec__q_0
 *
 * `this` is the struct VALUE and it is the `mkey`, so the predicate is matched
 * syntactically on it.  Writing ANY field of the struct -- even a scalar field
 * that has nothing to do with `q` -- produces a new struct value, and the
 * `__pred` sitting in the context is still keyed on the old one.  The two are
 * equal after unfolding, since they differ only in fields `__pred` does not
 * mention, but the prover does not unfold, and the function fails at its exit
 * with
 *
 *     Could not prove equality of
 *       'pts_to var_p (Mkstruct_s _s'13 val_p_0.struct_s__q)'
 *       'pts_to var_p val_p_0'
 *
 * Every one of these fails for that reason, which is why none of them is in
 * this file:
 *
 *     struct s1 { int a; const char *q; };
 *     void w1(struct s1 *p) { p->a = 1; }            // scalar write
 *     struct s2 { uint64_t bmap[1]; const char *q; };
 *     void w2(struct s2 *p) { p->bmap[0] = 1; }      // array write
 *     void w3(struct s2 *p) { fill_bmap(p->bmap, 1); } // array field to callee
 *
 * and `int *q` and `struct link *q` behave exactly as `const char *q` does.
 *
 * THE RULE
 * --------
 * If a struct field is a pointer the struct does not OWN -- a borrowed
 * reference to a longer-lived object, which is what most pointer fields in
 * systems code are -- mark it `_plain`.  `__pred` then collapses to `emp`, and
 * writes to the struct's other fields go through.  `_plain` is also the honest
 * model: without it, two structs pointing at the same table each claim
 * exclusive ownership of it.
 *
 * If the struct really does own the pointee, `_plain` is wrong and the write
 * has to be bracketed by an explicit unfold/fold of `__pred`.
 */
#include "pal.h"
#include <stdint.h>
#include <stddef.h>

#define ARRAY_SIZE(x) (sizeof(x) / sizeof(*(x)))

/* The callee: takes the array, not the container. */
static void fill_bmap(_array uint64_t *bmap, size_t n_words)
	_requires(n_words == 1)
	_preserves(bmap._length == 1)
{
	bmap[0] = 0;
	bmap[0] |= 1;
}

/* ---- no pointer fields: everything works ---- */

struct container {
	int a;
	uint64_t bmap[1];
	int b;
};

void use_inline(struct container *p)
{
	p->bmap[0] = 0;
	p->bmap[0] |= 1;
}

void use_one(struct container *p)
{
	fill_bmap(p->bmap, ARRAY_SIZE(p->bmap));
}

/*
 * Two calls in a row.  The second needs the array field's length, and a Pulse
 * call returns a FRESH existential spec which does not carry the
 * `full_array_lspec _ 1` refinement the field type had -- hence the
 * `_preserves(bmap._length == 1)` on `fill_bmap`.  Stated as a `_preserves`
 * rather than derived from `_requires(n_words == 1)`, because an `ensures` is
 * elaborated without the `requires` in scope.
 */
void use_two(struct container *p)
{
	fill_bmap(p->bmap, ARRAY_SIZE(p->bmap));
	fill_bmap(p->bmap, ARRAY_SIZE(p->bmap));
}

void use_then_write(struct container *p)
{
	fill_bmap(p->bmap, ARRAY_SIZE(p->bmap));
	p->b = 7;
}

/* ---- nesting ---- */

struct inner {
	int c;
	uint64_t bmap[1];
};

struct outer {
	int a;
	struct inner in;
	int b;
};

void use_nested_one(struct outer *p)
{
	fill_bmap(p->in.bmap, ARRAY_SIZE(p->in.bmap));
}

void use_nested_two(struct outer *p)
{
	fill_bmap(p->in.bmap, ARRAY_SIZE(p->in.bmap));
	fill_bmap(p->in.bmap, ARRAY_SIZE(p->in.bmap));
}

void use_nested_then_write(struct outer *p)
{
	fill_bmap(p->in.bmap, ARRAY_SIZE(p->in.bmap));
	p->in.c = 7;
}

struct inner2 {
	uint64_t bmap2[1];
};

struct mid {
	struct inner2 i2;
	uint64_t bmap[1];
};

struct outer3 {
	int a;
	struct mid m;
	int b;
};

/* Three levels, two arrays, and a write to a field of the outermost struct. */
void use_deep(struct outer3 *p)
{
	fill_bmap(p->m.bmap, ARRAY_SIZE(p->m.bmap));
	fill_bmap(p->m.i2.bmap2, ARRAY_SIZE(p->m.i2.bmap2));
	p->b = 3;
}

/* An array of structs alongside, which the callee never touches. */
struct link {
	uint64_t x;
	uint64_t y;
};

struct b_links {
	struct inner in;
	struct link links[4];
};

void use_b_links(struct b_links *p)
{
	fill_bmap(p->in.bmap, ARRAY_SIZE(p->in.bmap));
}

/* ---- pointer fields, marked `_plain` ---- */

/*
 * The same struct as `s2` in the header comment, which fails without the
 * annotation.  With it, `__pred` is `emp` and all three shapes go through.
 */
struct s_plain {
	int a;
	uint64_t bmap[1];
	_plain const char *q;
	_plain int *r;
	_plain struct link *s;
};

void write_plain_scalar(struct s_plain *p) { p->a = 1; }
void write_plain_array(struct s_plain *p)  { p->bmap[0] = 1; }
void use_plain(struct s_plain *p)          { fill_bmap(p->bmap, ARRAY_SIZE(p->bmap)); }

/* Nested, with the pointer fields on the outer struct -- the realistic shape. */
struct big_plain {
	uint64_t entry;
	unsigned char gid;
	struct inner in;
	unsigned int tlb_size;
	struct link links[4];
	_plain const char *log_str;
	uint64_t a0;
};

void use_big_plain(struct big_plain *p)
{
	fill_bmap(p->in.bmap, ARRAY_SIZE(p->in.bmap));
	p->in.c = 5;
	p->a0 = 1;
}
