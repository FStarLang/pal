#include "pal.h"
#include <stddef.h>
#include <stdint.h>

/* A mutable global. No function below owns it. */
uint32_t tag;

/* The callee only compares its arguments: it checks that two handles name the
 * same slot. It asks for nothing through either pointer. */
static void same_address(_plain uint32_t *p, _plain uint32_t *q)
    _requires(p != NULL && p == q) {
  (void)p;
  (void)q;
}

/* So a caller may pass `&tag` twice without owning `tag`. */
void pass_tag_address(void) { same_address(&tag, &tag); }

/* `pass_tag_address` demands nothing of `tag`: call it holding nothing. */
void check_pass_tag_address(void) {
  _ghost_stmt(Func_pass_tag_address.func_pass_tag_address ());
}

/* The same, when the other side of the comparison is a ghost: the callee's
 * other clauses speak of `g`, and `p` is only required to equal it. */
static void at_address(_plain uint32_t *p)
    _ghost_arg(uint32_t *g)
    _requires(p == g)
    _requires(_inline_pulse(pure (not (Pulse.Lib.C.Palow.Ptr.is_null $(g))))) {
  (void)p;
}

/* Only the caller knows which address `g` stands for, so it says so. */
void pass_tag_address_ghost(void) {
  _ghost_stmt($witness (hide addr_var_tag));
  at_address(&tag);
}

void check_pass_tag_address_ghost(void) {
  _ghost_stmt(Func_pass_tag_address_ghost.func_pass_tag_address_ghost ());
}
