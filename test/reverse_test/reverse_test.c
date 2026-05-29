#include "pal.h"
#include <stdint.h>
#include <stdlib.h>

void reverse(_array uint32_t *arr, size_t len)
  _preserves(arr._length == len)
  _ensures(_forall(size_t j, j < len ==> arr[j] == _old(arr[len - j - 1])))
{
  size_t i = 0;
  while (i < len / 2)
    _invariant(_live(i))
    _invariant(_live(*arr))
    _invariant(arr._length == len)
    _invariant(i <= len / 2)
    _invariant(_forall(size_t j, j < i || (len - 1 - i < j && j < len) ==> arr[j] == _old(arr[len - j - 1])))
    _invariant(_forall(size_t j, i <= j && j < len - i ==> arr[j] == _old(arr[j])))
  {
    size_t j = len - 1 - i;  
    uint32_t tmp = arr[i];
    arr[i] = arr[j];
    arr[j] = tmp;
    i = i + 1;
  }
}