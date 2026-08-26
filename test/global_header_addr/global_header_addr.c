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
 * The same bug on the value path: a pruned `const` global left the read
 * referring to a name that does not exist, which surfaces downstream as F*
 * Error 72.
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

/* 4.3 A global named in a *specification* is a variable reference too. Losing
 * it degraded the whole body to `admit()` rather than to a dangling name. */
uint32_t header_const_in_spec(void) _requires(h_const < 100) _ensures(return == h_const) {
  _ghost_stmt(Global_h_const.acquire_var_h_const());
  const uint32_t *p = &h_const;
  return *p;
  _ghost_stmt(drop_ (exists* q. pts_to Global_h_const.addr_var_h_const #q _));
}

/* ===========================================================================
 * 5 -- the same, without `extern`
 *
 * Prune splits on which file a declaration is in and never looks at storage
 * class, linkage or initialisers, so every kind of header global was lost
 * equally. The globals above are all `extern`, which would let a fix that only
 * covered `extern` pass; these pin the rest.
 *
 * Unlike section 4 these are defined, so their value is reachable directly
 * rather than only through an acquire.
 * ======================================================================== */

static const uint32_t m_static_const = 5;
const uint32_t m_plain_const = 7;
uint32_t m_tentative;
struct ms m_tentative_struct;

/* 5.1 `static const` in a header: internal linkage, value known. */
uint32_t read_header_static_const(void) _ensures(return == 5) { return h_static_const; }

/* 5.2 Control. */
uint32_t read_infile_static_const(void) _ensures(return == 5) { return m_static_const; }

/* 5.3 Plain `const` in a header: external linkage. */
uint32_t read_header_plain_const(void) _ensures(return == 7) { return h_plain_const; }

/* 5.4 Control. */
uint32_t read_infile_plain_const(void) _ensures(return == 7) { return m_plain_const; }

/* 5.5 A tentative definition is mutable, so it gets an address and no value. */
bool header_tentative_addr(void) _ensures(return == true) {
  uint32_t *p = &h_tentative;
  uint32_t *q = &h_tentative;
  return p == q;
}

/* 5.6 Control. */
bool infile_tentative_addr(void) _ensures(return == true) {
  uint32_t *p = &m_tentative;
  uint32_t *q = &m_tentative;
  return p == q;
}

/* 5.7 The same at struct type. */
bool header_tentative_struct_addr(void) _ensures(return == true) {
  struct hs *p = &h_tentative_struct;
  return p == &h_tentative_struct;
}

/* 5.8 Control. */
bool infile_tentative_struct_addr(void) _ensures(return == true) {
  struct ms *p = &m_tentative_struct;
  return p == &m_tentative_struct;
}
