/* Declarations for global_header_addr.c.
 *
 * The point of this file is that it is not the main file: prune keeps header
 * declarations only by reachability from the main file.
 */

#include <stdint.h>

struct hs {
  uint32_t x;
};

/* Mutable: address only, no `pts_to`. */
extern struct hs h_struct;
extern uint32_t h_mut;

/* `const`, so pure: address and value both usable. */
extern const uint32_t h_const;

/* `extern` is not what makes a header global vanish -- being in a header is --
 * so the same shapes are covered without it. These are definitions rather than
 * declarations, which is unusual in a header but is exactly the case under
 * test; this header has a single includer, and the test only compiles to an
 * object file. */
static const uint32_t h_static_const = 5; /* internal linkage       */
const uint32_t h_plain_const = 7;         /* external linkage       */
uint32_t h_tentative;                     /* tentative definition   */
struct hs h_tentative_struct;             /* tentative, struct type */
