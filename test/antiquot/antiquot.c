#include "pal.h"

void test_rvalue_antiquot(int *x)
    _ensures(_inline_pulse(pure (Int32.v $(*x) > 0)))
{
    _assert(_inline_pulse($&(x) |-> $(x) ** $&(*x) |-> $(*x)));
    *x = 6 + 7;
}

void test_ghost_stmt(int *x)
    _requires(*x == 0)
    _ensures(*x == 0)
{
    _ghost_stmt(rewrite (pure ($(*x) = $(*x))) as (pure ($(*x) = $(*x))));
    return;
}

typedef struct {
  int a;
  int b;
} my_pair;

// Test $type in a top-level _include_pulse block
_include_pulse(Antiquot_include1,
  let antiquot_type_test : Type0 = $type(int *)

  $declare(my_pair x)
  let test_access ($(x): $type(my_pair)) =
    $(x.a)

  $declare(my_pair x)
  let test_access_2 ($(x): $type(my_pair)) =
    $(x).$field(my_pair::a)
)

// Test $declare in a ghost_stmt
void test_declare(my_pair *x)
  _requires(x->a == 0)
  _ensures(x->a == 0)
{
  _ghost_stmt(assert pure (Antiquot_include1.test_access $(*x) == 0l));
  _ghost_stmt(assert pure (Antiquot_include1.test_access_2 $(*x) == 0l));
  return;
}

typedef union {
  int a;
  long b;
} my_union;

_include_pulse(Antiquot_include2,
  $declare(my_union x)

  let my_fun =
    $field(my_union::a)?

  let other_fun ($(x) : $type(my_union)) : prop =
    $(x.a._active)
)

void test_union() {
  my_union x;
  x.b = 1;
  _assert(!x.a._active);
  _ghost_stmt(assert pure (~(Antiquot_include2.other_fun $(x))));
}

// Test $unfold, $fold, $unfold-uninit, $fold-uninit antiquotations
_include_pulse(Antiquot_include3,
  let struct_unfold_name = $unfold(my_pair)
  let struct_fold_name = $fold(my_pair)
  let struct_unfold_uninit_name = $unfold-uninit(my_pair)
  let struct_fold_uninit_name = $fold-uninit(my_pair)
  let union_unfold_name = $unfold(my_union::a)
  let union_fold_name = $fold(my_union::a)
)

// Lexical antiquotations
_include_pulse(Antiquot_include4,
  ghost fn foo (x: ref int)
    preserves x |-> $`x // $`x is translated to 'x
  {}
)

_include_pulse(Antiquot_include5,
  let foo$`bar = 67 // translated to foo'bar
  let bar$` = 42 // bar$` is translated to bar'
)