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

/* Position 4: multi-character constant.  C leaves the value
   implementation-defined; clang and MSVC both pack the characters into an
   `int` most significant first, which is why on-media signatures are
   written this way -- a hex dump of the field spells the constant.  The
   contract has to agree with the body, so the same packing has to happen on
   both sides of the boundary: clang folds the one in the body, and PAL's own
   lexer folds the one in the contract. */
#define SIGNATURE_MACRO ('hdIR')

int32_t four_char_signature(void)
    _ensures(return == 'hdIR')
    _ensures(return == 0x68644952)
{
    return SIGNATURE_MACRO;
}

/* Fewer than four characters occupy the low-order bytes, so the constant is
   small and positive. */
int32_t two_char_signature(void)
    _ensures(return == 'AB')
    _ensures(return == 0x4142)
{
    return 'AB';
}


/* Hexadecimal and octal constants in a contract.  An on-media field is
   documented in hex, so a spec about one has to be writable in hex. */
int32_t mask_high_nibble(int32_t x)
    _requires(x >= 0 && x <= 0xFF)
    _ensures(return == x / 020)
{
    return x / 020;
}
