#include "pal.h"
#include <stdint.h>

/* CharacterLiteral test.

   The four cases below exercise the three positions in a C body that
   reach trRValue with a CharacterLiteral: return expression,
   arithmetic operand, and switch case label.

   Note on postconditions: the inline-Pulse spec parser in
   src/hauntedc.rs is a separate code path that doesn't yet recognise
   character literals at all, so we deliberately use the integer
   ASCII equivalents in _requires / _ensures. Supporting them in spec
   contexts would require new lexer + parser rules and is out of
   scope here. */

/* Position 1: return expression — plain CharacterLiteral as rvalue */
int32_t letter_a(void)
    _ensures(return == 65)
{
    return 'A';
}

int32_t newline_char(void)
    _ensures(return == 10)
{
    return '\n';
}

int32_t null_char(void)
    _ensures(return == 0)
{
    return '\0';
}

/* Position 2: inside an arithmetic expression — confirms the literal
   participates in binary ops the same way an IntegerLiteral does. */
int32_t alphabet_index(int32_t c)
    _requires(c >= 65 && c <= 90)
    _ensures(return == c - 65)
{
    return c - 'A';
}

/* Position 3: switch case label — case values also flow through
   trRValue (cpp/impl.cpp ~line 1096), so character literals must
   work as case labels too. */
int32_t classify_char(int32_t c)
    _ensures(c == 65 ==> return == 1)
    _ensures(c == 10 ==> return == 2)
    _ensures(c == 0  ==> return == 3)
{
    switch (c) {
    case 'A':  return 1;
    case '\n': return 2;
    case '\0': return 3;
    default:   return 0;
    }
}
