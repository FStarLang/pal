#include "pal.h"

/* Regression test: initializing a fixed-size char array from a shorter string
 * literal. Per C11 6.7.9p14/p21, the literal's bytes (including its NUL)
 * initialize the leading elements and the rest are zero. PAL emits a string
 * literal at length strlen+1 without consulting the destination array's
 * length, so a shorter literal must still be zero-padded out to that length.
 */

/* Case 1: padded array at top level (8 -> 16). */
_pure const char padded[16] = "packets";

char padded_first(void) _ensures(return == 112) { return padded[0];  }  /* 'p' */
char padded_last(void)  _ensures(return == 115) { return padded[6];  }  /* 's' */
char padded_nul(void)   _ensures(return == 0)   { return padded[7];  }  /* literal NUL */
char padded_tail(void)  _ensures(return == 0)   { return padded[15]; }  /* pad */

/* Case 2: exact fit (8 -> 8). Control: works today, must not regress. */
_pure const char exact[8] = "packets";

char exact_first(void) _ensures(return == 112) { return exact[0]; }
char exact_nul(void)   _ensures(return == 0)   { return exact[7]; }

/* Case 3: padded char array as a struct field. Two instances with
 * differently sized literals, so no field width makes both an exact fit.
 */
typedef struct {
    char desc[16];
} entry;

_pure const entry entry_packets = { "packets" };  /*  8 -> 16 */
_pure const entry entry_bytes   = { "bytes"   };  /*  6 -> 16 */

char entry_packets_first(void) _ensures(return == 112) { return entry_packets.desc[0];  }  /* 'p' */
char entry_packets_nul(void)   _ensures(return == 0)   { return entry_packets.desc[7];  }
char entry_packets_tail(void)  _ensures(return == 0)   { return entry_packets.desc[15]; }

char entry_bytes_first(void) _ensures(return == 98)  { return entry_bytes.desc[0];  }  /* 'b' */
char entry_bytes_nul(void)   _ensures(return == 0)   { return entry_bytes.desc[5];  }
char entry_bytes_tail(void)  _ensures(return == 0)   { return entry_bytes.desc[15]; }
