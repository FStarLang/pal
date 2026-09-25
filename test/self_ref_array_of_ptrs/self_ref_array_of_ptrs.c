#include "pal.h"

/* A self-referential struct with an _array field whose element type is a
   pointer to the same struct: the array element type must stay qualified in
   the generated typedef module. */
typedef struct node_t {
  struct node_t *next;
  _array struct node_t **to_nodes;
  _array double **from_values;
  int n;
} node_t;

int f1(node_t *p) _requires(p->to_nodes._length > 0) { return p->n; }

typedef struct node2_t {
  struct node2_t *next;
  _array double **vals;
  int n;
} node2_t;

int f2(node2_t *p) _requires(p->vals._length > 0) { return p->n; }

typedef struct node3_t {
  struct node3_t *next;
  int n;
} node3_t;

int f3(node3_t *p) { return p->n; }
