#include "pal.h"
#include <stddef.h>
#include <stdint.h>

/* A mutable global. No function below owns it. */
uint32_t tag;

/* The callee only requires that its argument is not NULL. It asks for nothing
 * through the pointer, as an allocator does with the address of a tag it
 * records but never dereferences. */
static void note_address(_plain uint32_t *p) _requires(p != NULL) { (void)p; }

/* So a caller may pass `&tag` without owning `tag`: it proves the requirement
 * from `addr_var_tag_not_null`. */
void pass_tag_address(void) { note_address(&tag); }

/* `pass_tag_address` demands nothing of `tag`: call it holding nothing. */
void check_pass_tag_address(void) {
  _ghost_stmt(Func_pass_tag_address.func_pass_tag_address ());
}
