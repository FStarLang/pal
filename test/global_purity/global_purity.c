/* Test: how PAL emits pure global variables -- their value and their address
 * machinery (`var_g`, `addr_var_g`, `addr_var_g_not_null`, `acquire_var_g`).
 *
 * A global is pure when it is `const`, or annotated `_pure`. `_pure` forces
 * purity outright, so `const` adds nothing under it.
 *
 * Cases are grouped by payload type, since emission differs: struct globals
 * get the full address machinery, array globals get none.
 *
 * Value and purity are properties of the object, not of one declaration, so
 * they should be read off the whole redeclaration chain (C17 6.9.2p2): a
 * chain with an initializer anywhere has that value, and a chain of bare
 * declarations is a tentative definition and reads as 0.
 *
 * PAL instead reads both from a single declaration, so cases 1.7, 1.8 and 1.9
 * do not verify yet. Each asserts the value C guarantees rather than what PAL
 * does today, so they come true once that is fixed.
 *
 *   1.7  const T g = V; const T g;   rejected; the initializer is lost
 *   1.8  _pure T g = V; _pure T g;   emits zero_default with no diagnostic,
 *                                    so it fails in F* rather than in PAL
 *   1.9  const T g;                  rejected, though C17 6.9.2p2 makes a
 *                                    tentative definition read as 0
 */

#include "pal.h"
#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>

/* ===========================================================================
 * Part 1 -- integers
 * ======================================================================== */

/* 1.1 `const` with an initializer, implicitly pure. */
const uint32_t i_const_init = 11;

uint32_t read_i_const_init(void) _ensures(return == 11) {
  _ghost_stmt(Global_i_const_init.acquire_var_i_const_init ());
  const uint32_t *p = &i_const_init;
  return *p;
  _ghost_stmt(drop_ (exists* q. pts_to Global_i_const_init.addr_var_i_const_init #q _));
}

/* 1.2 `_pure` with an initializer, on a type that is not `const`. */
_pure uint32_t i_pure_init = 22;

uint32_t read_i_pure_init(void) _ensures(return == 22) {
  _ghost_stmt(Global_i_pure_init.acquire_var_i_pure_init ());
  const uint32_t *p = &i_pure_init;
  return *p;
  _ghost_stmt(drop_ (exists* q. pts_to Global_i_pure_init.addr_var_i_pure_init #q _));
}

/* 1.3 A tentative definition: a file-scope global with no initializer and no
 * storage-class specifier is initialized as if by 0 (C17 6.9.2p2). */
_pure uint32_t i_pure_tentative;

uint32_t read_i_pure_tentative(void) _ensures(return == 0) {
  _ghost_stmt(Global_i_pure_tentative.acquire_var_i_pure_tentative ());
  const uint32_t *p = &i_pure_tentative;
  return *p;
  _ghost_stmt(drop_ (exists* q. pts_to Global_i_pure_tentative.addr_var_i_pure_tentative #q _));
}

/* 1.4 The same plus `const`, which must change nothing. Here to notice if
 * `const` ever starts meaning something under `_pure`. */
_pure const uint32_t i_pure_const_tentative;

uint32_t read_i_pure_const_tentative(void) _ensures(return == 0) {
  _ghost_stmt(Global_i_pure_const_tentative.acquire_var_i_pure_const_tentative ());
  const uint32_t *p = &i_pure_const_tentative;
  return *p;
  _ghost_stmt(drop_ (exists* q. pts_to Global_i_pure_const_tentative.addr_var_i_pure_const_tentative #q _));
}

/* 1.5 Declaration, then definition. Both name one object, so it must be
 * emitted once, carrying the definition's value. */
const uint32_t i_decl_then_def;
const uint32_t i_decl_then_def = 33;

uint32_t read_i_decl_then_def(void) _ensures(return == 33) {
  _ghost_stmt(Global_i_decl_then_def.acquire_var_i_decl_then_def ());
  const uint32_t *p = &i_decl_then_def;
  return *p;
  _ghost_stmt(drop_ (exists* q. pts_to Global_i_decl_then_def.addr_var_i_decl_then_def #q _));
}

/* 1.6 The same with `extern` on the declaration, which takes the linkage of
 * the prior declaration (C17 6.2.2p4) and so still names the object defined
 * here. */
extern const uint32_t i_extern_then_def;
const uint32_t i_extern_then_def = 44;

uint32_t read_i_extern_then_def(void) _ensures(return == 44) {
  _ghost_stmt(Global_i_extern_then_def.acquire_var_i_extern_then_def ());
  const uint32_t *p = &i_extern_then_def;
  return *p;
  _ghost_stmt(drop_ (exists* q. pts_to Global_i_extern_then_def.addr_var_i_extern_then_def #q _));
}

/* --- Declarations spread over several declarations. -----------------------
 *
 * Each asserts the value C guarantees.
 */

/* 1.7 Definition, then a bare re-declaration -- the mirror of 1.5. Legal C
 * naming one object, so the initializer from the first declaration is the
 * object's value. */
const uint32_t i_def_then_decl = 55;
const uint32_t i_def_then_decl;

uint32_t read_i_def_then_decl(void) _ensures(return == 55) {
  _ghost_stmt(Global_i_def_then_decl.acquire_var_i_def_then_decl ());
  const uint32_t *p = &i_def_then_decl;
  return *p;
  _ghost_stmt(drop_ (exists* q. pts_to Global_i_def_then_decl.addr_var_i_def_then_decl #q _));
}

/* 1.8 The same under `_pure`. Forcing purity must not lose the initializer:
 * the global still reads as 66. */
_pure uint32_t i_pure_def_then_decl = 66;
_pure uint32_t i_pure_def_then_decl;

uint32_t read_i_pure_def_then_decl(void) _ensures(return == 66) {
  _ghost_stmt(Global_i_pure_def_then_decl.acquire_var_i_pure_def_then_decl ());
  const uint32_t *p = &i_pure_def_then_decl;
  return *p;
  _ghost_stmt(drop_ (exists* q. pts_to Global_i_pure_def_then_decl.addr_var_i_pure_def_then_decl #q _));
}

/* 1.9 A bare `const` with no initializer anywhere. A tentative definition as
 * in 1.3, so it should read as 0 without needing `_pure`. */
const uint32_t i_bare_const;

uint32_t read_i_bare_const(void) _ensures(return == 0) {
  _ghost_stmt(Global_i_bare_const.acquire_var_i_bare_const ());
  const uint32_t *p = &i_bare_const;
  return *p;
  _ghost_stmt(drop_ (exists* q. pts_to Global_i_bare_const.addr_var_i_bare_const #q _));
}

/* ===========================================================================
 * Part 2 -- structs, which get the same address machinery as a scalar
 * ======================================================================== */

struct point {
  int32_t x;
  int32_t y;
};

/* 2.1 `const` with an initializer, read through its address. */
const struct point s_const_init = {.x = 3, .y = 4};

int32_t read_s_const_init(void) _ensures(return == 4) {
  _ghost_stmt(Global_s_const_init.acquire_var_s_const_init ());
  const struct point *p = &s_const_init;
  return p->y;
  _ghost_stmt(drop_ (exists* q. pts_to Global_s_const_init.addr_var_s_const_init #q _));
}

/* 2.2 A tentative definition, so every field reads as 0. */
_pure struct point s_pure_tentative;

int32_t read_s_pure_tentative(void) _ensures(return == 0) {
  _ghost_stmt(Global_s_pure_tentative.acquire_var_s_pure_tentative ());
  const struct point *p = &s_pure_tentative;
  return p->x;
  _ghost_stmt(drop_ (exists* q. pts_to Global_s_pure_tentative.addr_var_s_pure_tentative #q _));
}

/* 2.3 A declaration before the definition, as in 1.5. */
const struct point s_decl_then_def;
const struct point s_decl_then_def = {.x = 5, .y = 6};

int32_t read_s_decl_then_def(void) _ensures(return == 5) {
  _ghost_stmt(Global_s_decl_then_def.acquire_var_s_decl_then_def ());
  const struct point *p = &s_decl_then_def;
  return p->x;
  _ghost_stmt(drop_ (exists* q. pts_to Global_s_decl_then_def.addr_var_s_decl_then_def #q _));
}

/* ===========================================================================
 * Part 3 -- arrays
 *
 * An array global is emitted as a spec (`full_array_lspec`) rather than as
 * storage, so it is read with `array_spec_idx`, needs no ownership, and gets
 * no address machinery -- see `global_var_is_array` in src/ir/mod.rs.
 * ======================================================================== */

/* 3.1 `const` with an initializer. */
const uint32_t a_const_init[3] = {10, 20, 30};

uint32_t read_a_const_init(void) _ensures(return == 20) { return a_const_init[1]; }

/* 3.2 A tentative definition, so every element reads as 0. */
_pure const uint32_t a_pure_tentative[3];

uint32_t read_a_pure_tentative(void) _ensures(return == 0) { return a_pure_tentative[1]; }

/* 3.3 A declaration before the definition, as in 1.5. */
const uint32_t a_decl_then_def[3];
const uint32_t a_decl_then_def[3] = {7, 8, 9};

uint32_t read_a_decl_then_def(void) _ensures(return == 8) { return a_decl_then_def[1]; }
