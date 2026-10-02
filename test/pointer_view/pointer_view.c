// Test: `_pointer_view` — registering a typedef as the default view for a
// pointer's pointee.
//
// Covers:
//   1. A `_pointer_view` typedef (`list`) registers itself as the default view
//      for `node *`, so plain `node *` in signatures means the refined view.
//   2. `_plain node *` opts out and stays a bare pointer (struct field `next`
//      and the `ptr_is_null` parameter).
//   3. Inline-Pulse `$type(node *)` antiquotes are NOT viewed (stay `ref node`).
//
// This mirrors `recursive_struct`, but writes `node *` at use sites instead of
// the typedef name to exercise the substitution.

#include "pal.h"
#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>
#include <stdbool.h>

typedef struct node {
    int data;
    _plain struct node *next;
} node;

/* The list predicate has the same shape in both memory models; what differs
   is the vocabulary for "the object at this address", "the right to free it",
   "a points-to rules out null", the permission the refinement holds the list
   at, and the name of the ghost value it binds. Naming those once here keeps
   one copy of the predicate and its three ghost lemmas. */
#ifdef PALOW
#define _node_pts_to(h, nd) struct_node_pts_to h 1.0R nd
#define _node_freeable(h) freeable h struct_node_sizeof
#define _node_not_null(h) struct_node_pts_to_not_null h
#define _node_uninit(h) ptr_pts_to_uninit h
#define _node_perm 1.0R
#define _node_elements_of_head reveal val_head_elements
#else
#define _node_pts_to(h, nd) pts_to h nd
#define _node_freeable(h) freeable h
#define _node_not_null(h) Pulse.Lib.Reference.pts_to_not_null h
#define _node_uninit(h) pts_to_uninit h
#define _node_perm p
#define _node_elements_of_head reveal $`val_head_0
#endif

_include_pulse(Pointer_view_include1,
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

// Registered as the default view for `node *`.
_pointer_view
_refine_value(spec_list elements, _inline_pulse(Pointer_view_include1.is_list $(this) _node_perm $(elements)))
_refine_uninit(_inline_pulse(_node_uninit($(this))))
_plain
typedef struct node *list;

// `node *` here resolves to the `list` view.
_letimpure(spec_list _elements_of(const node *l),
  _inline_pulse(observe (Pointer_view_include1.is_list $(l) _)))

_include_pulse(Pointer_view_include2,
  ghost fn is_list_nil_case (head: $type(node *)) (#l: list Int32.t)
    preserves Pointer_view_include1.is_list head $`p l
    requires pure (is_null head)
    ensures pure (l == [])
  {
    match l {
      Nil -> { () }
      Cons hd tl -> {
        unfold (Pointer_view_include1.is_list head _ (hd :: tl));
        _node_not_null(head);
        unreachable ()
      }
    }
  }

  ghost fn elim_is_list_nonnull (head: $type(node *)) (#l: list Int32.t)
    requires Pointer_view_include1.is_list head $`p l ** pure (not (is_null head))
    ensures exists* (nd: $type(node)) (tl: list Int32.t).
      _node_pts_to(head, nd) ** _node_freeable(head) **
      pure (l == nd.$field(node::data) :: tl) **
      Pointer_view_include1.is_list nd.$field(node::next) $`p tl
  {
    match l {
      Nil -> { unfold (Pointer_view_include1.is_list head _ []); unreachable () }
      Cons hd tl -> { unfold (Pointer_view_include1.is_list head _ (hd :: tl)) }
    }
  }

  ghost fn intro_is_list_cons
    (head: $type(node *))
    (nd: $type(node))
    (#tl: list Int32.t)
    requires
      _node_pts_to(head, nd) **
      _node_freeable(head) **
      Pointer_view_include1.is_list nd.$field(node::next) $`p tl
    ensures Pointer_view_include1.is_list head $`p (nd.$field(node::data) :: tl)
  {
    fold (Pointer_view_include1.is_list head _ (nd.$field(node::data) :: tl))
  }
)

/* `_plain node *` opts out of the view: bare pointer, no ownership required. */
bool ptr_is_null(_plain node *n) {
    return n == NULL;
}

/* Recursive traversal: `node *` parameter resolves to the `list` view; the
 * `node *nx` local does too. */
_rec void traverse(const node *head)
    // Pulse can't currently prove termination from the opaque _elements_of
    // accessor, so we measure on the predicate's spec value directly.
    _decreases((spec_list) _inline_pulse(_node_elements_of_head))
{
    if (head == NULL) {
        _ghost_stmt(Pointer_view_include2.is_list_nil_case $(head));
        return;
    }
    _ghost_stmt(Pointer_view_include2.elim_is_list_nonnull $(head));
    node *nx = head->next;
    traverse(nx);
    _ghost_stmt(Pointer_view_include2.intro_is_list_cons $(head) $(*head));
}

_let(bool starts_with(spec_list xs, int x),
  _inline_pulse(match $(xs) with | [] -> 0=1 | hd::_ -> hd = $(x)))
_let(bool is_empty(spec_list xs), _inline_pulse($(xs) = []))

bool peek_head(const node *head, int *out)
  _ensures(return ==> starts_with(_elements_of(head), *out))
  _ensures(!return ==> is_empty(_elements_of(head)))
{
    if (head == NULL) {
        _ghost_stmt(Pointer_view_include2.is_list_nil_case $(head));
        return false;
    }
    _ghost_stmt(Pointer_view_include2.elim_is_list_nonnull $(head));
    *out = head->data;
    _ghost_stmt(Pointer_view_include2.intro_is_list_cons $(head) $(*head));
    return true;
}

void get_head(const node *head, _out int *out)
  _requires(head != NULL)
  _ensures(starts_with(_elements_of(head), *out))
{
    _ghost_stmt(Pointer_view_include2.elim_is_list_nonnull $(head));
    *out = head->data;
    _ghost_stmt(Pointer_view_include2.intro_is_list_cons $(head) $(*head));
}
