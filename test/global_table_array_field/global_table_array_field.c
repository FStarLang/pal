// A char-array field of a global struct table decayed to a pointer (#360).
#include "pal.h"

struct desc {
	char name[8];
	int offset;
};

static const struct desc table[2] = {
	{ "packets", 0 },
	{ "bytes", 8 },
};

void use_name(const char *s);
void use_str(_array const char *s) _requires(s._length == 8);
void use_desc(const struct desc *d);
void use_int(const int *x);
int log_args(_array const char *fmt, ...) _requires(fmt._length == 3);

// The issue's case: a field decayed into a one-object pointer.
_requires(j >= 0 && j < 2)
void pass_name(int j)
{
	use_name(table[j].name);
}

_requires(j >= 0 && j < 2)
void pass_str(int j)
{
	use_str(table[j].name);
}

void pass_const(void)
{
	use_name(table[1].name);
}

_requires(j >= 0 && j < 2)
void pass_entry(int j)
{
	use_desc(&table[j]);
}

_requires(j >= 0 && j < 2)
void pass_field(int j)
{
	use_int(&table[j].offset);
}

// IFB's `ethtool_sprintf(..., desc[j].desc)`: a variadic argument is the
// pointer itself.
_requires(j >= 0 && j < 2)
void pass_vararg(int j)
{
	log_args("%s", table[j].name);
}

// The same field of an entry the caller owns.
void pass_owned(const struct desc *d)
{
	use_name(d->name);
}
