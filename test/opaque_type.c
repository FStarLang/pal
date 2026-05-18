#include "pal.h"
#include <stdint.h>

// Define an opaque F* type alias
_type(my_list, list Int32.t)

// Use it in _include_pulse via $type
_include_pulse(Opaque_type_include,
  let empty_list : $type(my_list) = ([] #Int32.t)
)

// Basic _let usage
_let(my_list empty_list(), _inline_pulse([]))

// Use it as a _let return type with _inline_pulse in the body
_let(my_list make_singleton(int x),
  _inline_pulse(
    [$(x)] <: $type(my_list)
  )
)
