#include "pal.h"
#include <stdint.h>

static const int private_number = 1;
int shadowed_annotation(void) {
    { int private_number = 7; }
    _ghost_stmt(assert (pure ($(private_number) == 1)));
    return private_number;
}
int raw_private_reference(void) {
    _ghost_stmt(assert (pure (Global_private_number.var_private_number == 1)));
    return private_number;
}
int static_local(void) {
    static int value;
    return value;
}
typedef _plain int *annotated_pointer;
extern annotated_pointer annotation_object;
int __pal_tu_reserved;
int link_renamed(void) __asm__("native_renamed");
int reserved_local(int __pal_tu_parameter) {
    int __pal_tu_local = __pal_tu_parameter;
    return __pal_tu_local;
}
typedef _plain int *redeclared_pointer;
typedef _nullable int *redeclared_pointer;
