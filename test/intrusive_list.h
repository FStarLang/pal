#ifndef INTRUSIVE_LIST_H
#define INTRUSIVE_LIST_H

#include <stdbool.h>
#include "pal.h"

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

#endif
