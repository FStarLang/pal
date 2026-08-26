/* Test: pure global variables defined in another translation unit.
 *
 * `extern const T g;` is immutable, so it is a pure global -- but its value
 * lives in another translation unit. That value must be *assumed*
 * (`assume val var_g`), not invented: only a tentative definition is
 * guaranteed to be 0.
 *
 * Whether the object is external is a property of the whole build, not of one
 * file, so `merge` combines the declarations: a global is external only if no
 * file here defines it. Reads and the address machinery work either way.
 *
 * Part 1 globals are never defined, so no case may assert a number -- that is
 * the point. Part 2 globals are defined in another file of this same test, so
 * their cases assert the value exactly.
 *
 * Tentative definitions are not retested here; test/global_purity pins those.
 */

#include "pal.h"
#include <stdint.h>
#include <stddef.h>

/* ===========================================================================
 * Part 1 -- external, never defined in this build
 * ======================================================================== */

/* 1.1 `extern const`, pure by its type. The contract names the global itself,
 * which is the strongest thing sayable when the value is unknown. */
extern const uint32_t e_const;

uint32_t read_e_const(void) _ensures(return == e_const) {
  _ghost_stmt(Global_e_const.acquire_var_e_const ());
  const uint32_t *p = &e_const;
  return *p;
  _ghost_stmt(drop_ (exists* q. pts_to Global_e_const.addr_var_e_const #q _));
}

/* 1.2 `_pure` forcing purity on a type that is not `const`. */
_pure extern uint32_t e_pure;

uint32_t read_e_pure(void) _ensures(return == e_pure) {
  _ghost_stmt(Global_e_pure.acquire_var_e_pure ());
  const uint32_t *p = &e_pure;
  return *p;
  _ghost_stmt(drop_ (exists* q. pts_to Global_e_pure.addr_var_e_pure #q _));
}

/* 1.3 Both together, which must change nothing. */
_pure extern const uint32_t e_pure_const;

uint32_t read_e_pure_const(void) _ensures(return == e_pure_const) {
  _ghost_stmt(Global_e_pure_const.acquire_var_e_pure_const ());
  const uint32_t *p = &e_pure_const;
  return *p;
  _ghost_stmt(drop_ (exists* q. pts_to Global_e_pure_const.addr_var_e_pure_const #q _));
}

/* 1.4 The address of an external global: assumed like any other, and non-null,
 * since the object does exist in the defining unit. Read as "is it null?",
 * returning 1 for yes and 0 for no. */
extern const uint32_t e_addressed;

uint32_t *const p_to_e_addressed = (uint32_t *)&e_addressed;

uint32_t read_p_to_e_addressed(void) _ensures(return == 0) {
  _ghost_stmt(Global_p_to_e_addressed.acquire_var_p_to_e_addressed ());
  uint32_t *const *pp = &p_to_e_addressed;
  uint32_t *v = *pp;
  _ghost_stmt(drop_ (exists* q. pts_to Global_p_to_e_addressed.addr_var_p_to_e_addressed #q _));
  return (v == NULL) ? (uint32_t)1 : (uint32_t)0;
}

/* 1.5 An unknown value is still a single fixed value, so two reads agree. */
extern const uint32_t e_stable;

uint32_t e_stable_diff(void) _ensures(return == 0) {
  _ghost_stmt(Global_e_stable.acquire_var_e_stable ());
  const uint32_t *p = &e_stable;
  uint32_t first = *p;
  uint32_t second = *p;
  return first - second;
  _ghost_stmt(drop_ (exists* q. pts_to Global_e_stable.addr_var_e_stable #q _));
}

/* ===========================================================================
 * Part 2 -- declared here, defined in another file of this test
 *
 * A definition anywhere in the build supersedes the `extern` declarations of
 * it, so these read as their defined values rather than as assumed ones. The
 * defining file sorts before this one for `d_early_*` and after it for
 * `d_late_*`, which pins that the result does not depend on the order the
 * files reach PAL.
 * ======================================================================== */

/* 2.1 Defined in a file that PAL sees *before* this one. */
extern const uint32_t d_early_const;

uint32_t read_d_early_const(void) _ensures(return == 5) {
  _ghost_stmt(Global_d_early_const.acquire_var_d_early_const ());
  const uint32_t *p = &d_early_const;
  return *p;
  _ghost_stmt(drop_ (exists* q. pts_to Global_d_early_const.addr_var_d_early_const #q _));
}

/* 2.2 Defined in a file that PAL sees *after* this one. */
extern const uint32_t d_late_const;

uint32_t read_d_late_const(void) _ensures(return == 6) {
  _ghost_stmt(Global_d_late_const.acquire_var_d_late_const ());
  const uint32_t *p = &d_late_const;
  return *p;
  _ghost_stmt(drop_ (exists* q. pts_to Global_d_late_const.addr_var_d_late_const #q _));
}

/* 2.3 `_pure` on the declaration and not on the definition, as a header
 * annotating a global some other file defines. Purity is the object's, so it
 * survives the merge. */
_pure extern uint32_t d_early_pure;

uint32_t read_d_early_pure(void) _ensures(return == 7) {
  _ghost_stmt(Global_d_early_pure.acquire_var_d_early_pure ());
  const uint32_t *p = &d_early_pure;
  return *p;
  _ghost_stmt(drop_ (exists* q. pts_to Global_d_early_pure.addr_var_d_early_pure #q _));
}

/* 2.4 The address of a global defined in another file. */
extern const uint32_t d_early_addressed;

uint32_t *const p_to_d_early_addressed = (uint32_t *)&d_early_addressed;

uint32_t read_p_to_d_early_addressed(void) _ensures(return == 0) {
  _ghost_stmt(Global_p_to_d_early_addressed.acquire_var_p_to_d_early_addressed ());
  uint32_t *const *pp = &p_to_d_early_addressed;
  uint32_t *v = *pp;
  _ghost_stmt(
      drop_ (exists* q. pts_to Global_p_to_d_early_addressed.addr_var_p_to_d_early_addressed #q _));
  return (v == NULL) ? (uint32_t)1 : (uint32_t)0;
}
