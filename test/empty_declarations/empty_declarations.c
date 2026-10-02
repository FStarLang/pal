#include "pal.h"
#include <stdint.h>

;

int before_empty_declarations(void)
  _ensures(return == 7)
{
  return 7;
}

;;;

#define METADATA(value)
METADATA("empty");

#define DECLARE_VALUE(name) static const int name = 11;
DECLARE_VALUE(value);

int after_empty_declarations(void)
  _ensures(return == 11)
{
  return value;
}

int null_statement(void)
  _ensures(return == 13)
{
  ;
  return 13;
}

;
