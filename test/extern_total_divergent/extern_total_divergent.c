#include "pal.h"
#include <stdint.h>

_total
uint32_t external_total(uint32_t n)
    _ensures(return == n);

void reject_divergent_model(void)
{
    _ghost_stmt(ExternalModel.same_type
        Func_external_total.func_external_total ExternalModel.implementation);
}
