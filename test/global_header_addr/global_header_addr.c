/* Test: globals declared in a header rather than in the .c file.
 *
 * Regression test. Prune roots only main-file declarations and keeps header
 * ones by reachability, but `scan_expr` recorded no edge for a variable
 * reference, so a header-declared global was pruned away and `&g` emitted a
 * bare undefined identifier. Calls were unaffected, since call sites did
 * record an edge.
 *
 * Cases are paired: `h_` globals come from globals.h, `m_` ones from this
 * file. The pairs are otherwise identical, so the `m_` half is a control.
 *
 * Shapes mirror test/global_non_const_addr: a mutable global has no `pts_to`,
 * so it is exercised through pointer identity rather than by reading it.
 */

#include "pal.h"
#include <stdint.h>
#include <stdbool.h>

#include "globals.h"

struct ms {
  uint32_t x;
};

extern struct ms m_struct;
extern uint32_t m_mut;
extern const uint32_t m_const;

/* ===========================================================================
 * 1 -- address of a mutable global
 * ======================================================================== */

/* 1.1 The original report: before the fix `&h_mut` did not translate. */
bool header_addr_stable(void) _ensures(return == true) {
  uint32_t *p = &h_mut;
  uint32_t *q = &h_mut;
  return p == q;
}

/* 1.2 Control. */
bool infile_addr_stable(void) _ensures(return == true) {
  uint32_t *p = &m_mut;
  uint32_t *q = &m_mut;
  return p == q;
}

/* ===========================================================================
 * 2 -- address of a header global with a struct type
 *
 * The struct is reached through the global's *type* and was retained even
 * with the bug present; only the global itself was lost.
 * ======================================================================== */

/* 2.1 */
bool header_struct_addr(void) _ensures(return == true) {
  struct hs *p = &h_struct;
  return p == &h_struct;
}

/* 2.2 Control. */
bool infile_struct_addr(void) _ensures(return == true) {
  struct ms *p = &m_struct;
  return p == &m_struct;
}

/* ===========================================================================
 * 3 -- a header global's address in a global initialiser, reached while
 * scanning another declaration rather than a function body
 * ======================================================================== */

/* 3.1 */
uint32_t *const p_to_h_mut = &h_mut;

bool header_addr_via_global(void) _ensures(return == true) {
  _ghost_stmt(Global_p_to_h_mut.acquire_var_p_to_h_mut());
  uint32_t *const *pp = &p_to_h_mut;
  uint32_t *v = *pp;
  _ghost_stmt(drop_ (exists* q. pts_to Global_p_to_h_mut.addr_var_p_to_h_mut #q _));
  return v == &h_mut;
}

/* 3.2 Control. */
uint32_t *const p_to_m_mut = &m_mut;

bool infile_addr_via_global(void) _ensures(return == true) {
  _ghost_stmt(Global_p_to_m_mut.acquire_var_p_to_m_mut());
  uint32_t *const *pp = &p_to_m_mut;
  uint32_t *v = *pp;
  _ghost_stmt(drop_ (exists* q. pts_to Global_p_to_m_mut.addr_var_p_to_m_mut #q _));
  return v == &m_mut;
}

/* ===========================================================================
 * 4 -- reading a header `const` global
 *
 * The same bug on the value path: a pruned `const` global left the read with
 * nothing to refer to and the body was emitted as `admit()`.
 * ======================================================================== */

/* 4.1 */
uint32_t read_header_const(void) _ensures(return == h_const) {
  _ghost_stmt(Global_h_const.acquire_var_h_const());
  const uint32_t *p = &h_const;
  return *p;
  _ghost_stmt(drop_ (exists* q. pts_to Global_h_const.addr_var_h_const #q _));
}

/* 4.2 Control. */
uint32_t read_infile_const(void) _ensures(return == m_const) {
  _ghost_stmt(Global_m_const.acquire_var_m_const());
  const uint32_t *p = &m_const;
  return *p;
  _ghost_stmt(drop_ (exists* q. pts_to Global_m_const.addr_var_m_const #q _));
}

/* 4.3 A global named in a *specification* is a variable reference too. */
uint32_t header_const_in_spec(void) _requires(h_const < 100) _ensures(return == h_const) {
  _ghost_stmt(Global_h_const.acquire_var_h_const());
  const uint32_t *p = &h_const;
  return *p;
  _ghost_stmt(drop_ (exists* q. pts_to Global_h_const.addr_var_h_const #q _));
}
