// Reaching a struct field through a byte offset from the struct's address,
// with the offset taken from a constant descriptor table: the IFB driver's
// `ifb_fill_stats_data` (#358).
#include "pal.h"
#include <stdint.h>
#include <stddef.h>

typedef struct {
	uint64_t v;
} u64_stats_t;

uint64_t u64_stats_read(const u64_stats_t *p)
{
	return p->v;
}

struct q_stats {
	u64_stats_t packets;
	u64_stats_t bytes;
	uint32_t sync;
};

struct stats_desc {
	char desc[8];
	size_t offset;
};

static const struct stats_desc q_stats_desc[2] = {
	{ "packets", offsetof(struct q_stats, packets) },
	{ "bytes", offsetof(struct q_stats, bytes) },
};

// The pointer handed to a callee, at an offset read from the table.
void fill_stats_data(_array uint64_t *data, struct q_stats *q_stats)
	_requires(data._length == 2)
	_ensures(data._length == 2)
{
	void *stats_base = (void *)q_stats;
	int j;

	for (j = 0; j < 2; j++)
		_invariant(_live(j) && _live(*q_stats))
		_invariant(data._length == 2 && j >= 0 && j <= 2)
	{
		size_t offset = q_stats_desc[j].offset;
		data[j] = u64_stats_read((u64_stats_t *)(stats_base + offset));
	}
}

// A direct read, with the table subscripted in place.
_requires(j >= 0 && j < 2)
uint64_t read_stat(struct q_stats *q, int j)
{
	char *base = (char *)q;
	return ((u64_stats_t *)(base + q_stats_desc[j].offset))->v;
}

// A constant offset names one field.
uint32_t read_sync(struct q_stats *q)
	_ensures(return == q->sync)
{
	return *(uint32_t *)((char *)q + offsetof(struct q_stats, sync));
}

// A write through a computed offset.
_requires(j >= 0 && j < 2)
_ensures(q->sync == _old(q->sync))
void clear_stat(struct q_stats *q, int j)
{
	void *base = (void *)q;
	size_t offset = q_stats_desc[j].offset;
	*(u64_stats_t *)(base + offset) = (u64_stats_t){ 0 };
}

struct outer {
	uint32_t tag;
	struct q_stats rx;
	struct q_stats tx;
};

// A field of a nested structure, reached from the outer one: `tx.sync`.
_requires(off == 48)
uint32_t read_nested(struct outer *o, size_t off)
{
	return *(uint32_t *)((char *)o + off);
}

// A write with three candidates: `tag`, `rx.sync` and `tx.sync`.
_requires(off == 0 || off == 24 || off == 48)
void set_u32(struct outer *o, size_t off, uint32_t v)
{
	*(uint32_t *)((char *)o + off) = v;
}
