#pragma once

#include "pal.h"
#include <stdint.h>
#include <stdio.h>

typedef _array int *effective_int_array;
typedef _array double *effective_double_array;

int printf(const _array char *format, ...);

/* These cases only configure an opaque stdio handle without a user buffer. */
int setvbuf(_plain FILE *stream, _plain char *buffer, int mode, size_t size)
    _requires(buffer == NULL && mode == _IONBF && size == 0);
