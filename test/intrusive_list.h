#ifndef INTRUSIVE_LIST_H
#define INTRUSIVE_LIST_H

#include <stdbool.h>
#include "pal.h"

struct list_node {
    _plain struct list_node *next;
    _plain struct list_node *prev;
};

#define containing_record(ptr, type, field) _container_of(ptr, type, field)

_type(list_cells, list (ref Struct_list_node.struct_list_node))
_type(list_payload, IntrusiveList.payload)
_type(list_ref, ref Struct_list_node.struct_list_node)
_type(list_validation, IntrusiveListValidate.witness)

void list_init(_plain struct list_node *head)
    _requires(_inline_pulse(Pulse.Lib.Reference.pts_to_uninit $(head)))
    _ensures(_inline_pulse(IntrusiveList.is_list_ring $(head) 1.0R []));

bool list_empty(_plain const struct list_node *head)
    _ghost_arg(list_payload pl)
    _ghost_arg(list_cells cells)
    _requires(_inline_pulse(
        IntrusiveList.is_list_ring_with (reveal $(pl)) $(head) 1.0R (reveal $(cells))))
    _ensures(_inline_pulse(
        IntrusiveList.is_list_ring_with (reveal $(pl)) $(head) 1.0R (reveal $(cells))
        ** pure ($(return) <==> (reveal $(cells) == []))));

/* Check neighboring links of an initialized sentinel or linked entry. */
void list_validate(_plain const struct list_node *node)
    _ghost_arg(list_validation witness)
    _requires(_inline_pulse(
        IntrusiveListValidate.view $(node) (reveal $(witness))))
    _ensures(_inline_pulse(
        IntrusiveListValidate.view $(node) (reveal $(witness))));

/* Insertions require an entry that is not already linked into a list. */
void list_insert_head(_plain struct list_node *head, _plain struct list_node *entry)
    _ghost_arg(list_payload pl)
    _ghost_arg(list_cells cells)
    _requires(_inline_pulse(
        IntrusiveList.is_list_ring_with (reveal $(pl)) $(head) 1.0R (reveal $(cells))
        ** Pulse.Lib.Reference.pts_to_uninit $(entry) ** (reveal $(pl)) $(entry)))
    _ensures(_inline_pulse(
        IntrusiveList.is_list_ring_with (reveal $(pl)) $(head) 1.0R
            ($(entry) :: (reveal $(cells)))));
void list_insert_tail(_plain struct list_node *head, _plain struct list_node *entry)
    _ghost_arg(list_payload pl)
    _ghost_arg(list_cells cells)
    _requires(_inline_pulse(
        IntrusiveList.is_list_ring_with (reveal $(pl)) $(head) 1.0R (reveal $(cells))
        ** Pulse.Lib.Reference.pts_to_uninit $(entry) ** (reveal $(pl)) $(entry)))
    _ensures(_inline_pulse(
        IntrusiveList.is_list_ring_with (reveal $(pl)) $(head) 1.0R
            (FStar.List.Tot.append (reveal $(cells)) [$(entry)])));
void list_insert_after(_plain struct list_node *position, _plain struct list_node *entry)
    _ghost_arg(list_payload pl)
    _ghost_arg(list_ref head)
    _ghost_arg(list_cells front)
    _ghost_arg(list_cells back)
    _requires(_inline_pulse(
        IntrusiveList.is_list_ring_with (reveal $(pl)) (reveal $(head)) 1.0R
            (FStar.List.Tot.append (reveal $(front)) (reveal $(back)))
        ** pure ($(position) == IntrusiveList.last_or (reveal $(head)) (reveal $(front)))
        ** Pulse.Lib.Reference.pts_to_uninit $(entry) ** (reveal $(pl)) $(entry)))
    _ensures(_inline_pulse(
        IntrusiveList.is_list_ring_with (reveal $(pl)) (reveal $(head)) 1.0R
            (FStar.List.Tot.append (reveal $(front)) ($(entry) :: (reveal $(back))))));

/* The list must be nonempty. */
_plain struct list_node *list_remove_head(_plain struct list_node *head)
    _ghost_arg(list_payload pl)
    _ghost_arg(list_cells cells)
    _requires(_inline_pulse(
        IntrusiveList.is_list_ring_with (reveal $(pl)) $(head) 1.0R (reveal $(cells))
        ** pure ((reveal $(cells)) =!= [])))
    _ensures(_inline_pulse(
        IntrusiveList.is_list_ring_with (reveal $(pl)) $(head) 1.0R
            (match (reveal $(cells)) with | [] -> [] | _::rest -> rest)
        ** (exists* (next: IntrusiveList.lref).
            Pulse.Lib.Reference.pts_to $(return) (IntrusiveList.mklink next $(head)))
        ** (reveal $(pl)) $(return)
        ** pure ($(return) == IntrusiveList.first_or $(head) (reveal $(cells)))));

/* Entry must be linked and must not be the sentinel.
   Returns whether the list becomes empty. Does not clear entry's old links. */
bool list_remove(_plain struct list_node *entry)
    _ghost_arg(list_payload pl)
    _ghost_arg(list_ref head)
    _ghost_arg(list_cells front)
    _ghost_arg(list_cells back)
    _requires(_inline_pulse(
        IntrusiveList.is_list_ring_with (reveal $(pl)) (reveal $(head)) 1.0R
            (FStar.List.Tot.append (reveal $(front)) ($(entry) :: (reveal $(back))))))
    _ensures(_inline_pulse(
        IntrusiveList.is_list_ring_with (reveal $(pl)) (reveal $(head)) 1.0R
            (FStar.List.Tot.append (reveal $(front)) (reveal $(back)))
        ** Pulse.Lib.Reference.pts_to $(entry)
            (IntrusiveList.mklink
                (match (reveal $(back)) with | [] -> (reveal $(head)) | x::_ -> x)
                (IntrusiveList.last_or (reveal $(head)) (reveal $(front))))
        ** (reveal $(pl)) $(entry)
        ** pure ($(return) <==>
            (FStar.List.Tot.append (reveal $(front)) (reveal $(back)) == []))));

/* Append source to destination and empty source.
   The heads must belong to distinct, disjoint lists. */
void list_move(_plain struct list_node *source, _plain struct list_node *destination)
    _ghost_arg(list_payload pl)
    _ghost_arg(list_cells source_cells)
    _ghost_arg(list_cells destination_cells)
    _requires(_inline_pulse(
        IntrusiveList.is_list_ring_with (reveal $(pl)) $(source) 1.0R
            (reveal $(source_cells))
        ** IntrusiveList.is_list_ring_with (reveal $(pl)) $(destination) 1.0R
            (reveal $(destination_cells))))
    _ensures(_inline_pulse(
        IntrusiveList.is_list_ring_with (reveal $(pl)) $(source) 1.0R []
        ** IntrusiveList.is_list_ring_with (reveal $(pl)) $(destination) 1.0R
            (FStar.List.Tot.append (reveal $(destination_cells))
                (reveal $(source_cells)))));

#endif
