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
