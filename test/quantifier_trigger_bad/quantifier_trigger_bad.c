#include "pal.h"
#include <stddef.h>

/* A trigger is a term the solver matches on: it must mention the bound
   variable, be more than the variable itself, and not be a proposition. */
void unbound(_array const int *a, size_t n)
	_requires(a._length == n && n > 0)
	_requires(_forall(size_t k, _trigger(a[0]), k < n ==> a[k] == 0));

void bare(_array const int *a, size_t n)
	_requires(a._length == n)
	_requires(_forall(size_t k, _trigger(k), k < n ==> a[k] == 0));

void prop(_array const int *a, size_t n)
	_requires(a._length == n)
	_requires(_exists(size_t k, _trigger(a[k] == 0), k < n && a[k] == 0));
