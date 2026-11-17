#include "pal.h"
#include <stddef.h>
#include <stdint.h>

void init_optional_refined(
    int32_t value, _nullable _out _refine(*this == value) int32_t *p)
{
    if (p != NULL) {
        *p = value;
    }
}

void forward_optional_refined(
    int32_t value, _nullable _out _refine(*this == value) int32_t *p)
{
    init_optional_refined(value, p);
}

int32_t read_optional_refined(_nullable _refine(*this == 42) const int32_t *p)
    _ensures(return == 42)
{
    if (p != NULL) {
        return *p;
    }
    return 42;
}

void update_optional_refined(_nullable _refine(*this >= 0) int32_t *p)
{
    if (p != NULL) {
        *p = 42;
    }
}

void copy_optional_refined(
    const uint64_t *source,
    _nullable _out _refine(*this == *source) uint64_t *p)
{
    if (p != NULL) {
        *p = *source;
    }
}

void init_optional_refined_addressed(
    int32_t value, _nullable _out _refine(*this == value) int32_t *p)
{
    _assert(_live(p));
    if (p != NULL) {
        *p = value;
    }
}

void null_refined_division(
    uint32_t divisor,
    _nullable _out _refine(*this == 0u / divisor || *this != 0u / divisor) uint32_t *p)
    _requires(p == NULL)
{
    if (p != NULL) {
        *p = 0;
    }
}

void guarded_optional_refinement(
    uint32_t divisor,
    _nullable _out _refine(*this == 0u || *this == 84u / divisor) uint32_t *p)
{
    if (p != NULL) {
        *p = divisor == 0 ? 0 : 84u / divisor;
    }
}

// Keep zero symbolic: F* eagerly reduces a literal division by zero even
// inside the refinement's false non-null antecedent.
void call_optional_refined_null(uint32_t divisor)
    _requires(divisor == 0)
{
    init_optional_refined(42, NULL);
    null_refined_division(divisor, NULL);
}

int32_t call_optional_refined_nonnull(void)
    _ensures(return == 42)
{
    int32_t value;
    forward_optional_refined(42, &value);
    return value;
}
