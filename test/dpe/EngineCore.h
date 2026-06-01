#ifndef _ENGINE_CORE_H_
#define _ENGINE_CORE_H_

#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>
#include "pal.h"
#include "DPE.h"

bool engine_main(
    dice_digest cdi,
    const uds_array uds,
    const engine_record_t *record
);

#endif