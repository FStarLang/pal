/*
 * A mutable array global.
 *
 * PAL used to reject one outright, with two errors at once:
 *
 *   error: non-pure array globals are not yet supported
 *   error: cannot read the mutable global tbl; its address may be taken,
 *          but its value is not available
 *
 * The second objection does not apply to an array. C gives an array name no
 * value of its own: except as the operand of `sizeof` or `&`, it decays to a
 * pointer to its first element (C17 6.3.2.1p3). So there is nothing to "read",
 * and the name denotes the address -- which is exactly what an `_array T *`
 * parameter already is.
 *
 * A mutable array global is therefore emitted as storage of type
 * `array <elem>`, and its name as that address, so every existing array
 * operation applies to it unchanged.
 *
 * No ownership is handed out: PAL emits no acquire for a mutable global, so
 * without one supplied by the project there is no `array_pts_to` in existence
 * and the handle can be passed around but never dereferenced. `read_unowned`
 * below is the whole of what is free.
 */
#include "pal.h"
#include <stddef.h>
#include <stdint.h>

#define TBL_LEN 4

struct entry {
	uint64_t val;
	int tag;
};

static struct entry tbl[TBL_LEN];

/*
 * The project's own acquire. It is an `assume val`, sound only under the
 * discipline "acquire at most once per function, drop_ before every exit".
 *
 * It pins the length with `full_array_lspec ... TBL_LEN` rather than
 * `full_array_spec`. Without the pin, `array_spec_len` is an unconstrained
 * `nat` and a subscript fails with
 *   Failed to prove: array_spec_initd _v (SizeT.v i)
 * even with `i < TBL_LEN` in hand, because nothing connects TBL_LEN to the
 * array's extent. The length is a property of the ownership, not of the
 * handle, which is why PAL cannot state it for you.
 */
_include_pulse(ArrayGlobals,
  assume val acquire_var_tbl :
    (unit -> stt_ghost unit emp_inames emp
      (fun _ -> exists* (v: (full_array_lspec Struct_entry.struct_entry 4)).
         ((Pulse.Lib.C.Array.array_pts_to_full
             Global_tbl.addr_var_tbl 1.0R v))))
)

/* The address alone, with no ownership: legal, and useless on purpose. */
int read_unowned(void)
{
	_array struct entry *p = tbl;
	return p == 0;
}

uint64_t get(size_t i)
	_requires(i < TBL_LEN)
{
	_ghost_stmt(ArrayGlobals.acquire_var_tbl ());
	_array struct entry *p = tbl;
	uint64_t r = p[i].val;
	_ghost_stmt(drop_ (exists* (v: (full_array_lspec Struct_entry.struct_entry 4)).
		Pulse.Lib.C.Array.array_pts_to_full Global_tbl.addr_var_tbl 1.0R v));
	return r;
}

void set(size_t i, uint64_t v)
	_requires(i < TBL_LEN)
{
	_ghost_stmt(ArrayGlobals.acquire_var_tbl ());
	_array struct entry *p = tbl;
	p[i].val = v;
	_ghost_stmt(drop_ (exists* (v2: (full_array_lspec Struct_entry.struct_entry 4)).
		Pulse.Lib.C.Array.array_pts_to_full Global_tbl.addr_var_tbl 1.0R v2));
}

/* Subscripting the global directly, without naming a pointer first. */
int tag_of(size_t i)
	_requires(i < TBL_LEN)
{
	_ghost_stmt(ArrayGlobals.acquire_var_tbl ());
	int t = tbl[i].tag;
	_ghost_stmt(drop_ (exists* (v: (full_array_lspec Struct_entry.struct_entry 4)).
		Pulse.Lib.C.Array.array_pts_to_full Global_tbl.addr_var_tbl 1.0R v));
	return t;
}
