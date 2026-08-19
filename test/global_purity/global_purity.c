/* Test: how PAL emits pure global variables -- their value and their address
 * machinery (`var_g`, `addr_var_g`, `addr_var_g_not_null`, `acquire_var_g`).
 *
 * A global is pure when it is `const`, or annotated `_pure`. `_pure` forces
 * purity outright, so `const` adds nothing under it.
 *
 * Value and purity belong to the object, not to one declaration, so a global
 * declared several times is emitted once and takes its value from whichever
 * declaration carries the initializer. With no initializer anywhere it is a
 * tentative definition and reads as 0 (C17 6.9.2p2).
 *
 * Cases are grouped by payload type, since emission differs: struct globals
 * get the full address machinery, array globals get none, and pointer globals
 * are null unless they point at another global.
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

/* 1.3 A tentative definition: no initializer and no storage-class specifier,
 * so it is initialized as if by 0 (C17 6.9.2p2). */
_pure uint32_t i_pure_tentative;

uint32_t read_i_pure_tentative(void) _ensures(return == 0) {
  _ghost_stmt(Global_i_pure_tentative.acquire_var_i_pure_tentative ());
  const uint32_t *p = &i_pure_tentative;
  return *p;
  _ghost_stmt(drop_ (exists* q. pts_to Global_i_pure_tentative.addr_var_i_pure_tentative #q _));
}

/* 1.4 The same plus `const`, which must change nothing. */
_pure const uint32_t i_pure_const_tentative;

uint32_t read_i_pure_const_tentative(void) _ensures(return == 0) {
  _ghost_stmt(Global_i_pure_const_tentative.acquire_var_i_pure_const_tentative ());
  const uint32_t *p = &i_pure_const_tentative;
  return *p;
  _ghost_stmt(drop_ (exists* q. pts_to Global_i_pure_const_tentative.addr_var_i_pure_const_tentative #q _));
}

/* 1.5 Declaration, then definition: one object, emitted once. */
const uint32_t i_decl_then_def;
const uint32_t i_decl_then_def = 33;

uint32_t read_i_decl_then_def(void) _ensures(return == 33) {
  _ghost_stmt(Global_i_decl_then_def.acquire_var_i_decl_then_def ());
  const uint32_t *p = &i_decl_then_def;
  return *p;
  _ghost_stmt(drop_ (exists* q. pts_to Global_i_decl_then_def.addr_var_i_decl_then_def #q _));
}

/* 1.6 The same with `extern` on the declaration. */
extern const uint32_t i_extern_then_def;
const uint32_t i_extern_then_def = 44;

uint32_t read_i_extern_then_def(void) _ensures(return == 44) {
  _ghost_stmt(Global_i_extern_then_def.acquire_var_i_extern_then_def ());
  const uint32_t *p = &i_extern_then_def;
  return *p;
  _ghost_stmt(drop_ (exists* q. pts_to Global_i_extern_then_def.addr_var_i_extern_then_def #q _));
}

/* --- The same object declared more than once. ----------------------------- */

/* 1.7 Definition, then a bare re-declaration -- the mirror of 1.5. */
const uint32_t i_def_then_decl = 55;
const uint32_t i_def_then_decl;

uint32_t read_i_def_then_decl(void) _ensures(return == 55) {
  _ghost_stmt(Global_i_def_then_decl.acquire_var_i_def_then_decl ());
  const uint32_t *p = &i_def_then_decl;
  return *p;
  _ghost_stmt(drop_ (exists* q. pts_to Global_i_def_then_decl.addr_var_i_def_then_decl #q _));
}

/* 1.8 The same under `_pure`, which must not lose the initializer. */
_pure uint32_t i_pure_def_then_decl = 66;
_pure uint32_t i_pure_def_then_decl;

uint32_t read_i_pure_def_then_decl(void) _ensures(return == 66) {
  _ghost_stmt(Global_i_pure_def_then_decl.acquire_var_i_pure_def_then_decl ());
  const uint32_t *p = &i_pure_def_then_decl;
  return *p;
  _ghost_stmt(drop_ (exists* q. pts_to Global_i_pure_def_then_decl.addr_var_i_pure_def_then_decl #q _));
}

/* 1.9 A bare `const` with no initializer anywhere: a tentative definition as
 * in 1.3, so it reads as 0 without needing `_pure`. */
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
 * An array global is emitted as a spec rather than as storage, so it is read
 * with `array_spec_idx` and gets no address machinery.
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

/* ===========================================================================
 * Part 4 -- pointers
 *
 * Only a top-level `const` makes the object const, so `T *const p` is pure
 * while `const T *p` is not, and PAL rejects the latter as non-pure. A
 * pointer with no initializer is a tentative definition, so it is null. Each
 * case is read by the same predicate, "is this pointer null?", returning 1
 * for yes and 0 for no.
 * ======================================================================== */

/* 4.1 Top-level `const`, so pure. */
uint32_t *const p_const_null = NULL;

uint32_t read_p_const_null(void) _ensures(return == 1) {
  _ghost_stmt(Global_p_const_null.acquire_var_p_const_null ());
  uint32_t *const *pp = &p_const_null;
  uint32_t *v = *pp;
  _ghost_stmt(drop_ (exists* q. pts_to Global_p_const_null.addr_var_p_const_null #q _));
  return (v == NULL) ? (uint32_t)1 : (uint32_t)0;
}

/* 4.2 Both `const`s; the top-level one is what makes it pure. */
const uint32_t *const p_const_both = NULL;

uint32_t read_p_const_both(void) _ensures(return == 1) {
  _ghost_stmt(Global_p_const_both.acquire_var_p_const_both ());
  const uint32_t *const *pp = &p_const_both;
  const uint32_t *v = *pp;
  _ghost_stmt(drop_ (exists* q. pts_to Global_p_const_both.addr_var_p_const_both #q _));
  return (v == NULL) ? (uint32_t)1 : (uint32_t)0;
}

/* 4.3 A tentative definition, so null. */
_pure uint32_t *p_pure_tentative;

uint32_t read_p_pure_tentative(void) _ensures(return == 1) {
  _ghost_stmt(Global_p_pure_tentative.acquire_var_p_pure_tentative ());
  uint32_t *const *pp = &p_pure_tentative;
  uint32_t *v = *pp;
  _ghost_stmt(drop_ (exists* q. pts_to Global_p_pure_tentative.addr_var_p_pure_tentative #q _));
  return (v == NULL) ? (uint32_t)1 : (uint32_t)0;
}

/* 4.4 `_pure` forces purity on an object that is not itself `const`. */
_pure const uint32_t *p_pure_const_pointee;

uint32_t read_p_pure_const_pointee(void) _ensures(return == 1) {
  _ghost_stmt(Global_p_pure_const_pointee.acquire_var_p_pure_const_pointee ());
  const uint32_t *const *pp = &p_pure_const_pointee;
  const uint32_t *v = *pp;
  _ghost_stmt(drop_ (exists* q. pts_to Global_p_pure_const_pointee.addr_var_p_pure_const_pointee #q _));
  return (v == NULL) ? (uint32_t)1 : (uint32_t)0;
}

/* 4.5 Pointing at another global gives that address, not null. */
uint32_t *const p_addr_of_global = (uint32_t *)&i_pure_init;

uint32_t read_p_addr_of_global(void) _ensures(return == 0) {
  _ghost_stmt(Global_p_addr_of_global.acquire_var_p_addr_of_global ());
  uint32_t *const *pp = &p_addr_of_global;
  uint32_t *v = *pp;
  _ghost_stmt(drop_ (exists* q. pts_to Global_p_addr_of_global.addr_var_p_addr_of_global #q _));
  return (v == NULL) ? (uint32_t)1 : (uint32_t)0;
}

