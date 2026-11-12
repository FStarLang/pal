#include "pal.h"
#include <stddef.h>
#include <stdint.h>

/* Each step of a walked pointer is stated from the array's ownership
   (`array_walk_next`), so a loop's invariant `walk_ok` for the stepped pointer
   does not depend on the solver multiplying positions by the element size. */

/* A step with no access in the same iteration. */
uint64_t nth(_array const uint64_t *s, size_t n)
	_requires(n < s._length)
	_ensures(return == s[n])
{
	const uint64_t *p = s;
	for (size_t i = 0; i < n; i++)
		_invariant(i <= n && p - s == i)
		p++;
	return *p;
}

/* `p += 2`: a constant step of more than one element. */
void zero_even(_array uint64_t *d, size_t n)
	_requires(2 * n <= d._length && d._length <= 1000000)
	_ensures(d._length == _old(d._length))
	_ensures(_forall(size_t k, k < n ==> d[2 * k] == 0))
{
	uint64_t *p = d;
	for (size_t i = 0; i < n; i++, p += 2)
		_invariant(i <= n && p - d == 2 * i)
		_invariant(_forall(size_t k, k < i ==> d[2 * k] == 0))
		*p = 0;
}

/* `p = p + k`: a step by a computed count. */
uint32_t every(_array const uint32_t *s, size_t k, size_t n)
	_requires(0 < k && k * n < s._length && s._length <= 1000000)
	_ensures(return == s[k * n])
{
	const uint32_t *p = s;
	for (size_t i = 0; i < n; i++)
		_invariant(i <= n && p - s == k * i)
		p = p + k;
	return *p;
}

/* musl's `wmemcpy` shape, both pointers stepped in one expression. */
void copy(_array uint32_t *restrict d, _array const uint32_t *restrict s, size_t n)
	_requires(n <= d._length && n <= s._length && d._length <= 1000000)
	_ensures(d._length == _old(d._length))
	_ensures(_forall(size_t k, k < n ==> d[k] == s[k]))
{
	uint32_t *a = d;
	for (; n; n--)
		_invariant(d - a == s - _old(s) && d - a + n == _old(n))
		_invariant(_forall(_specint k, 0 <= k && k < d - a ==> a[k] == _old(s)[k]))
		*d++ = *s++;
}
