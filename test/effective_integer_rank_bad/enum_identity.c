#include "pal.h"

enum first_kind { FIRST_ZERO };
enum second_kind { SECOND_ZERO };

enum second_kind read_other_enum(enum first_kind *p)
{
    return *(enum second_kind *)p;
}
