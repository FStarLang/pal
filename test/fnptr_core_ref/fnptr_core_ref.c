#include "pal.h"
#include <stdint.h>

// Function-pointer parameter attributes must survive Clang type translation.
// Erasing this back-pointer breaks the otherwise recursive F* module dependency
// between Struct_parent and Struct_callbacks.
struct parent;

struct callbacks {
    void (*visit)(_core_ref struct parent *parent);
};

struct parent {
    uint32_t value;
    struct callbacks callbacks;
};

// The same annotation must survive when the function pointer is introduced
// through a typedef rather than written directly as a field type.
struct typedef_parent;
typedef void (*visit_fn)(_core_ref struct typedef_parent *parent);

struct typedef_callbacks {
    visit_fn visit;
};

struct typedef_parent {
    uint32_t value;
    struct typedef_callbacks callbacks;
};
