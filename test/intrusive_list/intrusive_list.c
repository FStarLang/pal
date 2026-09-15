#include <assert.h>
#include "list.h"
#include "pal.h"

/* Nodes and the sentinel are caller-owned; no allocation or freeing occurs. */

void list_init(_plain struct list_node *head)
{
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold_uninit $(head));
    head->next = head;
    head->prev = head;
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(head));
    _ghost_stmt(IntrusiveList.ring_intro_empty IntrusiveList.no_payload $(head));
}

bool list_empty(_plain const struct list_node *head)
{
    _ghost_stmt(IntrusiveList.ring_open (reveal $(pl)) $(head));
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(head));
    return head->next == head;
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(head));
    _ghost_stmt(IntrusiveList.ring_close (reveal $(pl)) $(head));
}

void list_validate(_plain const struct list_node *node)
{
    _ghost_stmt(IntrusiveListValidate.view_open_all $(node));
    assert(node->next->prev == node);
    assert(node->prev->next == node);
    _ghost_stmt(IntrusiveListValidate.view_close_all $(node));
}

void list_insert_after(_plain struct list_node *position, _plain struct list_node *entry)
{
    _ghost_stmt(IntrusiveListValidate.ring_view (reveal $(pl)) (reveal $(head))
        $(position) (reveal $(front)) (reveal $(back)));
    list_validate(position);
    _ghost_stmt(IntrusiveListValidate.restore_ring (reveal $(pl)) (reveal $(head))
        $(position) (FStar.List.Tot.append (reveal $(front)) (reveal $(back))));
    _ghost_stmt(IntrusiveListOps.position_open (reveal $(pl)) (reveal $(head))
        $(position) (reveal $(front)) (reveal $(back)));
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(position));
    struct list_node *next = position->next;
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(position));
    _ghost_stmt(IntrusiveListOps.position_close (reveal $(pl)) (reveal $(head))
        $(position) $(next) (reveal $(front)) (reveal $(back)));
    _ghost_stmt(IntrusiveList.split_pl_out (reveal $(pl)) (reveal $(head)) 1.0R
        $(position) $(next) (reveal $(front)) (reveal $(back)));
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold_uninit $(entry));
    entry->prev = position;
    entry->next = next;
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(entry));
    _ghost_stmt(IntrusiveList.add_expose_next (reveal $(head)) $(position) $(next)
        (reveal $(front)) (reveal $(back)));
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(next));
    next->prev = entry;
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(next));
    _ghost_stmt(IntrusiveList.add_reseat (reveal $(head)) $(position) $(next) $(entry)
        (reveal $(front)) (reveal $(back)));
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(position));
    position->next = entry;
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(position));
    _ghost_stmt(IntrusiveList.add_close (reveal $(head)) $(position) $(next) $(entry)
        (reveal $(front)) (reveal $(back)));
    _ghost_stmt(IntrusiveList.payload_of_insert (reveal $(pl))
        (reveal $(front)) (reveal $(back)) $(entry));
    _ghost_stmt(IntrusiveList.ring_pl_in (reveal $(pl)) (reveal $(head)) 1.0R
        (FStar.List.Tot.append (reveal $(front)) ($(entry) :: (reveal $(back)))));
}

void list_insert_head(_plain struct list_node *head, _plain struct list_node *entry)
{
    _ghost_stmt(IntrusiveListOps.insert_head_prepare (reveal $(pl)) $(head)
        (reveal $(cells)));
    list_insert_after(head, entry);
}

void list_insert_tail(_plain struct list_node *head, _plain struct list_node *entry)
{
    _ghost_stmt(IntrusiveListValidate.sentinel_view (reveal $(pl)) $(head) (reveal $(cells)));
    list_validate(head);
    _ghost_stmt(IntrusiveListValidate.restore_ring (reveal $(pl)) $(head)
        $(head) (reveal $(cells)));
    _ghost_stmt(IntrusiveList.ring_open (reveal $(pl)) $(head));
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(head));
    struct list_node *tail = head->prev;
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(head));
    _ghost_stmt(IntrusiveList.ring_close (reveal $(pl)) $(head));
    _ghost_stmt(IntrusiveListOps.insert_tail_prepare (reveal $(pl)) $(head)
        (reveal $(cells)));
    list_insert_after(tail, entry);
}

bool list_remove(_plain struct list_node *entry)
{
    _ghost_stmt(IntrusiveListValidate.member_view (reveal $(pl)) (reveal $(head))
        $(entry) (reveal $(front)) (reveal $(back)));
    list_validate(entry);
    _ghost_stmt(IntrusiveListValidate.restore_ring (reveal $(pl)) (reveal $(head))
        $(entry) (FStar.List.Tot.append (reveal $(front)) ($(entry) :: (reveal $(back)))));
    _ghost_stmt(IntrusiveList.ring_pl_out (reveal $(pl)) (reveal $(head)) 1.0R
        (FStar.List.Tot.append (reveal $(front)) ($(entry) :: (reveal $(back)))));
    _ghost_stmt(IntrusiveList.payload_of_remove (reveal $(pl))
        (reveal $(front)) (reveal $(back)) $(entry));
    _ghost_stmt(IntrusiveList.del_open (reveal $(head)) $(entry)
        (reveal $(front)) (reveal $(back)));
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(entry));
    struct list_node *previous = entry->prev;
    struct list_node *next = entry->next;
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(entry));
    _ghost_stmt(IntrusiveList.del_cut_pin (reveal $(head)) $(previous) $(next) $(entry)
        (reveal $(front)) (reveal $(back)));
    _ghost_stmt(IntrusiveList.del_expose_prev (reveal $(head)) $(previous) $(next) $(entry)
        (reveal $(front)) (reveal $(back)));
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(previous));
    previous->next = next;
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(previous));
    _ghost_stmt(IntrusiveList.del_reseat_next (reveal $(head)) $(previous) $(next) $(entry)
        (reveal $(front)) (reveal $(back)));
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(next));
    next->prev = previous;
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(next));
    _ghost_stmt(IntrusiveList.del_close_next (reveal $(head)) $(previous) $(next) $(entry)
        (reveal $(front)) (reveal $(back)));
    _ghost_stmt(IntrusiveList.ring_pl_in (reveal $(pl)) (reveal $(head)) 1.0R
        (FStar.List.Tot.append (reveal $(front)) (reveal $(back))));
    return previous == next;
}

_plain struct list_node *list_remove_head(_plain struct list_node *head)
{
    _ghost_stmt(IntrusiveListValidate.sentinel_view (reveal $(pl)) $(head) (reveal $(cells)));
    list_validate(head);
    _ghost_stmt(IntrusiveListValidate.restore_ring (reveal $(pl)) $(head)
        $(head) (reveal $(cells)));
    _ghost_stmt(IntrusiveList.ring_open_full (reveal $(pl)) $(head));
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(head));
    struct list_node *first = head->next;
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(head));
    _ghost_stmt(IntrusiveList.ring_close (reveal $(pl)) $(head));
    _ghost_stmt(IntrusiveListOps.remove_head_prepare (reveal $(pl)) $(head)
        $(first) (reveal $(cells)));
    list_remove(first);
    return first;
}

void list_move(_plain struct list_node *source, _plain struct list_node *destination)
{
    bool empty = list_empty(source);
    if (empty) {
        _ghost_stmt(IntrusiveListOps.move_empty (reveal $(pl)) $(source) $(destination)
            (reveal $(source_cells)) (reveal $(destination_cells)));
        return;
    } else {
        _ghost_stmt(IntrusiveListOps.nonempty_intro (reveal $(pl)) $(source)
            (reveal $(source_cells)));
    }

    _ghost_stmt(IntrusiveListOps.nonempty_elim (reveal $(pl)) $(source)
        (reveal $(source_cells)));
    _ghost_stmt(IntrusiveList.ring_open_full (reveal $(pl)) $(source));
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(source));
    struct list_node *first = source->next;
    struct list_node *last = source->prev;
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(source));
    _ghost_stmt(IntrusiveList.ring_close (reveal $(pl)) $(source));
    _ghost_stmt(IntrusiveList.ring_open (reveal $(pl)) $(destination));
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(destination));
    struct list_node *tail = destination->prev;
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(destination));
    _ghost_stmt(IntrusiveList.ring_close (reveal $(pl)) $(destination));
    _ghost_stmt(IntrusiveListOps.move_open (reveal $(pl)) $(source) $(destination)
        $(first) $(last) $(tail) (reveal $(source_cells)) (reveal $(destination_cells)));
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(tail));
    tail->next = first;
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(tail));
    _ghost_stmt(IntrusiveListOps.move_first (reveal $(pl)) $(source) $(destination)
        $(first) $(last) $(tail) (reveal $(source_cells)) (reveal $(destination_cells)));
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(first));
    first->prev = tail;
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(first));
    _ghost_stmt(IntrusiveListOps.move_last (reveal $(pl)) $(source) $(destination)
        $(first) $(last) $(tail) (reveal $(source_cells)) (reveal $(destination_cells)));
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(last));
    last->next = destination;
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(last));
    _ghost_stmt(IntrusiveListOps.move_destination (reveal $(pl)) $(source) $(destination)
        $(first) $(last) $(tail) (reveal $(source_cells)) (reveal $(destination_cells)));
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(destination));
    destination->prev = last;
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(destination));
    _ghost_stmt(IntrusiveListOps.move_close (reveal $(pl)) $(source) $(destination)
        $(first) $(last) $(tail) (reveal $(source_cells)) (reveal $(destination_cells)));
    list_init(source);
    _ghost_stmt(IntrusiveList.ring_empty_repl IntrusiveList.no_payload
        (reveal $(pl)) $(source));
}
