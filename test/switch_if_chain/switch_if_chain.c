#include "pal.h"
#include <stdint.h>

/* A switch with no fall-through and a default arm is an if/else chain. Emitted
 * that way, each branch condition tests the scrutinee directly, which is what
 * the postcondition is phrased in; the general encoding's hit/break flags hid
 * it behind compound conditions over mutable state. */
uint32_t decode(uint32_t tag)
    _ensures(tag == 1 ==> return == 10)
    _ensures(tag == 2 ==> return == 20)
    _ensures(tag != 1 && tag != 2 ==> return == 0)
{
    uint32_t r;
    switch (tag) {
    case 1:
        r = 10;
        break;
    case 2:
        r = 20;
        break;
    default:
        r = 0;
        break;
    }
    return r;
}
