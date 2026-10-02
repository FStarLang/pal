// Test: recursive (self-referential) struct — e.g., a linked-list node.
//
// Covers:
//   1. Struct definition with self-referential pointer field
//   2. Field reads/writes on recursive struct (auto-generated ownership)
//   3. _include_pulse with recursive predicate over the struct
//   4. _rec with _plain: recursive traversal passes field read to recursive call
//      (regression: fn_decl must be elaborated before pre-registration so
//       recursive calls don't get spurious Unknown→Ref casts + assert False)
//   5. Null checks on recursive struct pointers
//   6. _ghost_stmt proof steps interleaved with C field access

#include "pal.h"
#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>
#include <stdbool.h>

typedef struct node {
    int data;
    _plain struct node *next;
} node;

/* 1–2. Basic field read/write */
void set_data(node *n, int x) {
    n->data = x;
}

int get_data(node *n) {
    return n->data;
}

/* The list predicate has the same shape in both memory models; what differs
   is the vocabulary for "the object at this address", "the right to free it",
   and "a points-to rules out null". Naming those three once here keeps one
   copy of the predicate and its three ghost lemmas. */
#ifdef PALOW
#define _node_pts_to(h, nd) struct_node_pts_to h 1.0R nd
#define _node_freeable(h) freeable h struct_node_sizeof
#define _node_not_null(h) struct_node_pts_to_not_null h
#define _node_uninit(h) ptr_pts_to_uninit h
/* The permission the refinement holds the list at. The old model names the
   one its generated typedef predicate is parameterised by; Palow states the
   ownership directly, at the full permission `_node_pts_to` uses. */
#define _node_perm 1.0R
/* The ghost value the list refinement binds, as the measure for `traverse`.
   Each model has its own name for it: the old one auto-binds a ticked
   variable, Palow makes it an erased implicit named after the parameter and
   the refinement. */
#define _node_elements_of_head reveal val_head_elements
#else
#define _node_pts_to(h, nd) pts_to h nd
#define _node_freeable(h) freeable h
#define _node_not_null(h) Pulse.Lib.Reference.pts_to_not_null h
#define _node_uninit(h) pts_to_uninit h
#define _node_perm p
#define _node_elements_of_head reveal $`val_head_0
#endif

/* 3. _include_pulse: recursive ownership predicate + ghost helpers.
 *    Tests that pal generates correct struct types and that _include_pulse
 *    can define recursive predicates over self-referential structs. */
_include_pulse(Recursive_struct_include1,
  module L = FStar.List.Tot

  let rec is_list ([@@@mkey] head: $type(node *)) (p: perm) (l: list Int32.t)
    : Tot slprop (decreases l)
  = match l with
    | [] -> pure (is_null head)
    | hd :: tl ->
      exists* (nd: $type(node)).
        _node_pts_to(head, nd) **
        _node_freeable(head) **
        pure (nd.$field(node::data) == hd) **
        is_list nd.$field(node::next) p tl
)

_type(spec_list, list Int32.t)

_refine_value(spec_list elements, _inline_pulse(Recursive_struct_include1.is_list $(this) _node_perm $(elements)))
_refine_uninit(_inline_pulse(_node_uninit($(this))))
_plain
typedef struct node *list;

_letimpure(spec_list _elements_of(const list l),
  _inline_pulse(observe (Recursive_struct_include1.is_list $(l) _)))

_include_pulse(Recursive_struct_include2,
  ghost fn is_list_nil_case (head: $type(node *)) (#l: list Int32.t)
    preserves Recursive_struct_include1.is_list head $`p l
    requires pure (is_null head)
    ensures pure (l == [])
  {
    match l {
      Nil -> { () }
      Cons hd tl -> {
        unfold (Recursive_struct_include1.is_list head _ (hd :: tl));
        _node_not_null(head);
        unreachable ()
      }
    }
  }

  ghost fn elim_is_list_nonnull (head: $type(node *)) (#l: list Int32.t)
    requires Recursive_struct_include1.is_list head $`p l ** pure (not (is_null head))
    ensures exists* (nd: $type(node)) (tl: list Int32.t).
      _node_pts_to(head, nd) ** _node_freeable(head) **
      pure (l == nd.$field(node::data) :: tl) **
      Recursive_struct_include1.is_list nd.$field(node::next) $`p tl
  {
    match l {
      Nil -> { unfold (Recursive_struct_include1.is_list head _ []); unreachable () }
      Cons hd tl -> { unfold (Recursive_struct_include1.is_list head _ (hd :: tl)) }
    }
  }

  ghost fn intro_is_list_cons
    (head: $type(node *))
    (nd: $type(node))
    (#tl: list Int32.t)
    requires
      _node_pts_to(head, nd) **
      _node_freeable(head) **
      Recursive_struct_include1.is_list nd.$field(node::next) $`p tl
    ensures Recursive_struct_include1.is_list head $`p (nd.$field(node::data) :: tl)
  {
    fold (Recursive_struct_include1.is_list head _ (nd.$field(node::data) :: tl))
  }
)

/* 4. _rec with _plain: recursive call passes struct field read (head->next)
 *    to _plain parameter. Regression: without elaborating fn_decl types before
 *    pre-registration, this gets a spurious (node[?]) cast → assert False. */
_rec void traverse(const list head)
    // Pulse can't currently prove termination from the opaque _elements_of
    // accessor, so we measure on the predicate's spec value directly.
    _decreases((spec_list) _inline_pulse(_node_elements_of_head))
{
    if (head == NULL) {
        _ghost_stmt(Recursive_struct_include2.is_list_nil_case $(head));
        return;
    }
    _ghost_stmt(Recursive_struct_include2.elim_is_list_nonnull $(head));
    node *nx = head->next;
    traverse(nx);
    _ghost_stmt(Recursive_struct_include2.intro_is_list_cons $(head) $(*head));
}

_let(bool starts_with(spec_list xs, int x),
  _inline_pulse(match $(xs) with | [] -> 0=1 | hd::_ -> hd = $(x)))
_let(bool is_empty(spec_list xs), _inline_pulse($(xs) = []))

/* 5–6. _ghost_stmt with raw_unfold/fold around field reads and null check */
bool peek_head(const list head, int *out)
  _ensures(return ==> starts_with(_elements_of(head), *out))
  _ensures(!return ==> is_empty(_elements_of(head)))
{
    if (head == NULL) {
        _ghost_stmt(Recursive_struct_include2.is_list_nil_case $(head));
        return false;
    }
    _ghost_stmt(Recursive_struct_include2.elim_is_list_nonnull $(head));
    *out = head->data;
    _ghost_stmt(Recursive_struct_include2.intro_is_list_cons $(head) $(*head));
    return true;
}

void get_head(const list head, _out int *out)
  _requires(head != NULL)
  _ensures(starts_with(_elements_of(head), *out))
{
    _ghost_stmt(Recursive_struct_include2.elim_is_list_nonnull $(head));
    *out = head->data;
    _ghost_stmt(Recursive_struct_include2.intro_is_list_cons $(head) $(*head));
}
