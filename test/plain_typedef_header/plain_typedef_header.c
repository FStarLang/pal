#include "node.h"

// A `_plain` typedef in an included header marks the struct plain even
// though no declaration in this file mentions it: `struct node` has no
// ownership predicate, so its `gate` may be null, or shared, after a call.

void detach(struct node *n)
  _ensures(n->gate == NULL)
{
  n->gate = NULL;
}

void share(struct node *n, struct node *m)
  _ensures(n->gate == m->gate)
{
  n->gate = m->gate;
}

void use(void)
{
  struct node a;
  struct node b;
  a.x = 3;
  a.gate = NULL;
  b.x = 4;
  b.gate = NULL;
  share(&a, &b);
  detach(&a);
}
