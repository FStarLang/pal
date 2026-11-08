#include "pal.h"
#include <stdint.h>

uint32_t external_loop(uint32_t n)
    _ensures(return == n);

_total
uint32_t external_total(uint32_t n)
    _ensures(return == n);

uint32_t defined_here(uint32_t n)
    _ensures(return == n);

uint32_t defined_here(uint32_t n)
{
    return n;
}

uint32_t middle(uint32_t n)
    _ensures(return == n)
{
    return external_loop(n);
}

uint32_t outer(uint32_t n)
    _ensures(return == n)
{
    return middle(n);
}

void check_model(void)
{
    _ghost_stmt(ExternalModel.same_type
        Func_external_loop.func_external_loop ExternalModel.implementation);
    _ghost_stmt(ExternalModel.same_type
        Func_middle.func_middle ExternalModel.implementation);
    _ghost_stmt(ExternalModel.same_type
        Func_outer.func_outer ExternalModel.implementation);
    _ghost_stmt(ExternalModel.same_type
        ExternalModel.total_implementation Func_external_total.func_external_total);
    _ghost_stmt(ExternalModel.same_type
        ExternalModel.total_implementation Func_defined_here.func_defined_here);
}
