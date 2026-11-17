#ifndef DLL_H
#define DLL_H

#include <stdbool.h>
#include "pal.h"

/* Intrusive, caller-owned circular doubly linked lists. */
struct list_node {
    _plain struct list_node *next;
    _plain struct list_node *prev;
};

#define containing_record(ptr, type, field) _container_of(ptr, type, field)

_type(list_context, IntrusiveListContext.context)
_type(list_insertion, IntrusiveListContext.insertion)
_type(list_cut, IntrusiveListContext.cut)
_type(list_validation, IntrusiveListContext.validation)
_type(list_movement, IntrusiveListContext.movement)

void list_init(_plain struct list_node *head)
    _ghost_arg(list_context ctx)
    _requires(_inline_pulse(IntrusiveListContext.init_pre (reveal $(ctx)) $(head)))
    _ensures(_inline_pulse(IntrusiveListContext.ring (reveal $(ctx)) $(head)));

bool list_empty(_plain const struct list_node *head)
    _ghost_arg(list_context ctx)
    _requires(_inline_pulse(
        IntrusiveListContext.ring (reveal $(ctx)) $(head)))
    _ensures(_inline_pulse(
        IntrusiveListContext.empty_post (reveal $(ctx)) $(head) $(return)));

/* Check neighboring links of an initialized sentinel or linked entry. */
void list_validate(_plain const struct list_node *node)
    _ghost_arg(list_validation ctx)
    _requires(_inline_pulse(
        IntrusiveListContext.validation_pre (reveal $(ctx)) $(node)))
    _ensures(_inline_pulse(
        IntrusiveListContext.validation_pre (reveal $(ctx)) $(node)));

/* Insertions require an entry that is not already linked into a list. */
void list_insert_head(_plain struct list_node *head, _plain struct list_node *entry)
    _ghost_arg(list_insertion ctx)
    _requires(_inline_pulse(
        IntrusiveListContext.insert_pre (reveal $(ctx)) $(head) $(entry)))
    _ensures(_inline_pulse(
        IntrusiveListContext.insert_head_post (reveal $(ctx)) $(head) $(entry)));
void list_insert_tail(_plain struct list_node *head, _plain struct list_node *entry)
    _ghost_arg(list_insertion ctx)
    _requires(_inline_pulse(
        IntrusiveListContext.insert_pre (reveal $(ctx)) $(head) $(entry)))
    _ensures(_inline_pulse(
        IntrusiveListContext.insert_tail_post (reveal $(ctx)) $(head) $(entry)));
void list_insert_after(_plain struct list_node *position, _plain struct list_node *entry)
    _ghost_arg(list_cut ctx)
    _requires(_inline_pulse(
        IntrusiveListContext.insert_after_pre (reveal $(ctx)) $(position) $(entry)))
    _ensures(_inline_pulse(
        IntrusiveListContext.insert_after_post (reveal $(ctx)) $(entry)));

/* The list must be nonempty. */
_plain struct list_node *list_remove_head(_plain struct list_node *head)
    _ghost_arg(list_context ctx)
    _requires(_inline_pulse(
        IntrusiveListContext.remove_head_pre (reveal $(ctx)) $(head)))
    _ensures(_inline_pulse(
        IntrusiveListContext.remove_head_post (reveal $(ctx)) $(head) $(return)));

/* Entry must be linked and must not be the sentinel.
   Returns whether the list becomes empty. Does not clear entry's old links. */
bool list_remove(_plain struct list_node *entry)
    _ghost_arg(list_cut ctx)
    _requires(_inline_pulse(
        IntrusiveListContext.remove_pre (reveal $(ctx)) $(entry)))
    _ensures(_inline_pulse(
        IntrusiveListContext.remove_post (reveal $(ctx)) $(entry) $(return)));

/* Append source to destination and empty source.
   The heads must belong to distinct, disjoint lists. */
void list_move(_plain struct list_node *source, _plain struct list_node *destination)
    _ghost_arg(list_movement ctx)
    _requires(_inline_pulse(
        IntrusiveListContext.move_pre (reveal $(ctx)) $(source) $(destination)))
    _ensures(_inline_pulse(
        IntrusiveListContext.move_post (reveal $(ctx)) $(source) $(destination)));


/* Integer-item client: exact sequence and ownership contracts. */
struct item {
    int value;
    struct list_node link;
};

#define item_from_link(ptr) containing_record(ptr, struct item, link)

_type(item_entries, Dll.Client.entries)

/* First match, or NULL. The result remains borrowed from the unchanged list. */
_plain struct item *items_find(_plain struct list_node *head, int value)
    _ghost_arg(item_entries entries)
    _requires(_inline_pulse(
        IntrusiveListIndexed.is_list_ring_ix Dll.Client.item_ipl
            $(head) 1.0R (reveal $(entries))))
    _ensures(_inline_pulse(
        IntrusiveListIndexed.is_list_ring_ix Dll.Client.item_ipl
            $(head) 1.0R (reveal $(entries)) **
        pure ($(return) == Dll.Client.first_match $(value) (reveal $(entries)))));

/* NULL on an empty list; otherwise transfers ownership of the whole first item. */
_plain struct item *items_pop_front(_plain struct list_node *head)
    _ghost_arg(item_entries entries)
    _requires(_inline_pulse(
        IntrusiveListIndexed.is_list_ring_ix Dll.Client.item_ipl
            $(head) 1.0R (reveal $(entries))))
    _ensures(_inline_pulse(
        Dll.Client.pop_post $(head) (reveal $(entries)) $(return)));

/* Stable insertion into an already sorted list, consuming the detached item. */
void items_insert_sorted(_plain struct list_node *head, _plain struct item *item)
    _ghost_arg(item_entries entries)
    _ghost_arg(int description)
    _requires(_inline_pulse(
        IntrusiveListIndexed.is_list_ring_ix Dll.Client.item_ipl
            $(head) 1.0R (reveal $(entries)) **
        (exists* (link: Struct_list_node.struct_list_node).
            Dll.Client.item_pts_to $(item)
                (Dll.Client.item_record (reveal $(description)) link)) **
        pure (IntrusiveListIndexed.sorted Dll.Client.value_le (reveal $(entries)))))
    _ensures(_inline_pulse(
        IntrusiveListIndexed.is_list_ring_ix Dll.Client.item_ipl
            $(head) 1.0R
            (IntrusiveListIndexed.insert Dll.Client.value_le
                (Dll.Client.item_link $(item))
                (reveal $(description)) (reveal $(entries))) **
        pure (IntrusiveListIndexed.sorted Dll.Client.value_le
            (IntrusiveListIndexed.insert Dll.Client.value_le
                (Dll.Client.item_link $(item))
                (reveal $(description)) (reveal $(entries))))));

/* Order-preserving filter. Returns ownership of all matching items, not memory
   deallocation: callers retain their addresses and remain responsible for them. */
void items_remove_value(_plain struct list_node *head, int value)
    _ghost_arg(item_entries entries)
    _requires(_inline_pulse(
        IntrusiveListIndexed.is_list_ring_ix Dll.Client.item_ipl
            $(head) 1.0R (reveal $(entries))))
    _ensures(_inline_pulse(
        IntrusiveListIndexed.is_list_ring_ix Dll.Client.item_ipl
            $(head) 1.0R
            (IntrusiveListIndexed.without (Dll.Client.matches_value $(value))
                (reveal $(entries))) **
        Dll.Client.detached
            (IntrusiveListIndexed.matching (Dll.Client.matches_value $(value))
                (reveal $(entries))) **
        pure (Dll.Client.first_match $(value)
            (IntrusiveListIndexed.without (Dll.Client.matches_value $(value))
                (reveal $(entries))) == null)));

/* Closed stack-allocated client: every sentinel and item is recovered. */
void list_example(void)
    _requires(_inline_pulse(emp))
    _ensures(_inline_pulse(emp));

#endif
