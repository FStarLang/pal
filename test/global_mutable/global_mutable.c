/* Test: mutable global variables under the bring-your-own-permission model.
 *
 * A mutable global `g` emits only its address (`assume val addr_var_g : ref t`)
 * and no permission for it. Reads and writes go through that address, and the
 * permission is threaded by hand: every function that touches `g` names it with
 * `_live(g)` in its contract, and the entrypoint assumes it.
 */

#include "pal.h"
#include <stdint.h>
#include <stdbool.h>

/* Neither `const` nor `_pure`, so PAL treats these as mutable globals. */
bool x;
uint32_t counter;

/* 1.1 Reading a mutable global needs its permission and gives it back. */
bool read_x(void) _requires(_live(x)) _ensures(_live(x))
    _ensures(return == _old(x)) {
  return x;
}

/* 1.2 Writing one too; the write is visible in the postcondition. */
void set_x(bool v) _requires(_live(x)) _ensures(_live(x)) _ensures(x == v) {
  x = v;
}

/* 2.1 A read-modify-write on an integer global. */
void bump(void) _requires(_live(counter)) _requires(counter < 100)
    _ensures(_live(counter)) _ensures(counter == _old(counter) + 1) {
  counter = counter + 1;
}

/* 2.2 Permission threads through a call: the caller holds `_live`, hands it to
 * the callee, and gets it back. */
void bump_twice(void) _requires(_live(counter)) _requires(counter < 99)
    _ensures(_live(counter)) _ensures(counter == _old(counter) + 2) {
  bump();
  bump();
}

/* 3.1 The address of a mutable global is still one fixed address, and writing
 * through it writes the global. */
void set_x_via_ptr(bool v) _requires(_live(x)) _ensures(_live(x))
    _ensures(x == v) {
  bool *p = &x;
  *p = v;
}

/* 4.1 An entrypoint assumes the permission for the globals it uses, and gives
 * it back on return: Pulse rejects a function that leaks ownership. */
int main(void) _requires(_live(x)) _requires(_live(counter)) _ensures(_live(x))
    _ensures(_live(counter)) {
  set_x(true);
  counter = 0;
  bump_twice();
  return read_x() ? 0 : 1;
}

/* 5.1 A struct-typed mutable global: `_live` covers the whole object, and
 * fields are reached through the same address. */
struct point {
  uint32_t px;
  uint32_t py;
};

struct point origin;

struct screen_state { struct point inner; } screen;

uint32_t *y_address(void)
    _ensures(_inline_pulse(rewrites_to $(return) (Global_screen.addr_var_screen +!
        Struct_point.struct_point_offsetof_py))) {
  return &screen.inner.py;
}

bool is_y_address(_plain uint32_t *p)
    _ensures(_inline_pulse(pure ($(return) <==> $(p) == (Global_screen.addr_var_screen +!
        Struct_point.struct_point_offsetof_py)))) {
  return p == &screen.inner.py;
}

/* The publishing interfaces can be used without any permission for screen. */
void check_y_address(void) {
  _ghost_stmt(let p = Func_y_address.func_y_address ();
              let yes = Func_is_y_address.func_is_y_address p;
              assert pure yes);
}

static _plain uint32_t *identity(_plain uint32_t *p) _ensures(return == p) { return p; }

_plain uint32_t *publish_y(void)
    _ensures(_inline_pulse(rewrites_to $(return) (Global_screen.addr_var_screen +!
        Struct_point.struct_point_offsetof_py))) {
  return identity(&screen.inner.py);
}

void check_publish_y(void) {
  _ghost_stmt(let p = Func_publish_y.func_publish_y ();
              let yes = Func_is_y_address.func_is_y_address p;
              assert pure yes);
}

static uint32_t read_plain(_plain uint32_t *p)
    _ghost_arg(uint32_t value)
    _preserves(_inline_pulse(uint32_t_pts_to $(p) 1.0R $(value)))
    _ensures(return == value) {
  return *p;
}

uint32_t read_counter_via_call(void) {
  return read_plain(&counter);
}

/* Publishing the address does not borrow the struct. */
struct point *origin_address(void)
    _ensures(_inline_pulse(pure ($(return) == Global_origin.addr_var_origin))) {
  return &origin;
}

void move_x(uint32_t dx) _requires(_live(origin)) _requires(origin.px < 100)
    _requires(dx < 100) _ensures(_live(origin))
    _ensures(origin.px == _old(origin.px) + dx)
    _ensures(origin.py == _old(origin.py)) {
  origin.px = origin.px + dx;
}
