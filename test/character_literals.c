#include "pal.h"
#include <stdint.h>

/* CharacterLiteral test.

   The four cases below exercise the three positions in a C body that
   reach trRValue with a CharacterLiteral: return expression,
   arithmetic operand, and switch case label.

/* Position 1: return expression — plain CharacterLiteral as rvalue */
int32_t letter_a(void)
    _ensures(return == 'A')
{
    return 'A';
}

int32_t newline_char(void)
    _ensures(return == '\n')
{
    return '\n';
}

int32_t null_char(void)
    _ensures(return == '\0')
{
    return '\0';
}

/* Position 2: inside an arithmetic expression — confirms the literal
   participates in binary ops the same way an IntegerLiteral does. */
int32_t alphabet_index(int32_t c)
    _requires(c >= 'A' && c <= 'Z')
    _ensures(return == c - 'A')
{
    return c - 'A';
}

/* Position 3: switch case label */
int32_t classify_char(int32_t c)
    _ensures(c == 'A'  ==> return == 1)
    _ensures(c == '\n' ==> return == 2)
    _ensures(c == '\0' ==> return == 3)
{
    switch (c) {
    case 'A':  return 1;
    case '\n': return 2;
    case '\0': return 3;
    default:   return 0;
    }
    return 0;
}
