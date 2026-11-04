#ifndef C2PULSE
#include <stdint.h>
int32_t genuine_a(void), genuine_b(void), object_a(void), object_b(void);
int32_t header_a(void), header_b(void), pointer_a(void), annotated_a(void);
int32_t parameter_shadow(int32_t), block_shadow(void), call_external(void);
int32_t false_function_a(void), false_function_b(void);
int32_t false_object_a(void), false_object_b(void);
int32_t *address_a(void), *address_b(void);
int32_t array_a(void), array_b(void), external_object(void);
int32_t write_a(void), write_b(void);
int main(void) {
    return !(genuine_a() == 1 && genuine_b() == 2 &&
             object_a() == 1 && object_b() == 2 &&
             header_a() == 1 && header_b() == 2 &&
             address_a() != address_b() &&
             write_a() == 1 && write_b() == 2 &&
             *address_a() == 1 && *address_b() == 2 &&
             pointer_a() == 1 && annotated_a() == 1 &&
             parameter_shadow(9) == 9 && block_shadow() == 1 &&
             call_external() == 3 &&
             array_a() == 3 && array_b() == 4 && external_object() == 5 &&
             false_function_a() == 1 && false_function_b() == 2 &&
             false_object_a() == 1 && false_object_b() == 2);
}
#endif
