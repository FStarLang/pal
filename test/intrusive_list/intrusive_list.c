#include <assert.h>
#include "list.h"
#include "pal.h"

/* Nodes and the sentinel are caller-owned; no allocation or freeing occurs. */

/* Expand proof parameters in annotations without materializing erased values. */
#define LIST_CTX (reveal $(ctx))
#define LIST_MODEL (LIST_CTX.IntrusiveListContext.model)
#define LIST_PAYLOAD (LIST_MODEL.IntrusiveListContext.resource)
#define LIST_HEAD (LIST_CTX.IntrusiveListContext.head)
#define LIST_FRONT (LIST_CTX.IntrusiveListContext.front)
#define LIST_BACK (LIST_CTX.IntrusiveListContext.back)
#define LIST_DESCRIPTION (LIST_CTX.IntrusiveListContext.description)
#define LIST_ENTRIES (LIST_MODEL.IntrusiveListContext.entries)
#define LIST_RING_PAYLOAD (LIST_CTX.IntrusiveListContext.resource)
#define LIST_RING_ENTRIES (LIST_CTX.IntrusiveListContext.entries)
#define LIST_APPEND(front_, back_) (FStar.List.Tot.append (front_) (back_))
#define LIST_CUT(model_, head_, front_, back_, description_) \
    { IntrusiveListContext.model = model_; IntrusiveListContext.head = head_; \
      IntrusiveListContext.front = front_; IntrusiveListContext.back = back_; \
      IntrusiveListContext.description = description_; }
#define LIST_SOURCE (LIST_CTX.IntrusiveListContext.source)
#define LIST_SOURCE_PAYLOAD (LIST_SOURCE.IntrusiveListContext.resource)
#define LIST_SOURCE_ENTRIES (LIST_SOURCE.IntrusiveListContext.entries)
#define LIST_DESTINATION_ENTRIES (LIST_CTX.IntrusiveListContext.destination_entries)

void list_init(_plain struct list_node *head)
{
    _ghost_stmt(unfold (IntrusiveListContext.init_pre LIST_CTX $(head)));
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold_uninit $(head));
    head->next = head;
    head->prev = head;
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(head));
    _ghost_stmt(IntrusiveListIndexed.ring_intro_empty LIST_CTX.IntrusiveListContext.resource $(head));
    _ghost_stmt(rewrite (IntrusiveListIndexed.is_list_ring_ix LIST_CTX.IntrusiveListContext.resource
        $(head) 1.0R []) as (IntrusiveListIndexed.is_list_ring_ix LIST_CTX.IntrusiveListContext.resource
        $(head) 1.0R LIST_CTX.IntrusiveListContext.entries));
    _ghost_stmt(IntrusiveListContext.prepare_ring LIST_CTX $(head));
}

bool list_empty(_plain const struct list_node *head)
{
    _ghost_stmt(IntrusiveListContext.finish_ring LIST_CTX $(head));
    _ghost_stmt(IntrusiveListIndexed.ring_open LIST_CTX.IntrusiveListContext.resource $(head));
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(head));
    return head->next == head;
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(head));
    _ghost_stmt(IntrusiveListIndexed.ring_close LIST_CTX.IntrusiveListContext.resource $(head));
    _ghost_stmt(IntrusiveListContext.prepare_ring LIST_CTX $(head));
    _ghost_stmt(fold (IntrusiveListContext.empty_post LIST_CTX $(head) $(return)));
}

void list_validate(_plain const struct list_node *node)
{
    _ghost_stmt(unfold (IntrusiveListContext.validation_pre LIST_CTX $(node)));
    _ghost_stmt(IntrusiveListContext.finish_ring LIST_MODEL LIST_HEAD);
    _ghost_stmt(rewrite (IntrusiveListIndexed.is_list_ring_ix LIST_PAYLOAD LIST_HEAD 1.0R LIST_ENTRIES)
        as (IntrusiveListIndexed.is_list_ring_ix LIST_PAYLOAD LIST_HEAD 1.0R LIST_APPEND(LIST_FRONT, LIST_BACK)));
    _ghost_stmt(IntrusiveListValidate.ring_view LIST_PAYLOAD LIST_HEAD $(node) LIST_FRONT LIST_BACK);
    _ghost_stmt(IntrusiveListValidate.view_open_all $(node));
    assert(node->next->prev == node);
    assert(node->prev->next == node);
    _ghost_stmt(IntrusiveListValidate.view_close_all $(node));
    _ghost_stmt(IntrusiveListValidate.restore_ring LIST_PAYLOAD LIST_HEAD $(node) LIST_APPEND(LIST_FRONT, LIST_BACK));
    _ghost_stmt(rewrite (IntrusiveListIndexed.is_list_ring_ix LIST_PAYLOAD LIST_HEAD 1.0R LIST_APPEND(LIST_FRONT, LIST_BACK))
        as (IntrusiveListIndexed.is_list_ring_ix LIST_PAYLOAD LIST_HEAD 1.0R LIST_ENTRIES));
    _ghost_stmt(IntrusiveListContext.prepare_ring LIST_MODEL LIST_HEAD);
    _ghost_stmt(fold (IntrusiveListContext.validation_pre LIST_CTX $(node)));
}

void list_insert_after(_plain struct list_node *position, _plain struct list_node *entry)
{
    _ghost_stmt(unfold (IntrusiveListContext.insert_after_pre LIST_CTX $(position) $(entry)));
    _ghost_stmt(IntrusiveListContext.finish_ring LIST_MODEL LIST_HEAD);
    _ghost_stmt(rewrite (IntrusiveListIndexed.is_list_ring_ix LIST_PAYLOAD LIST_HEAD 1.0R LIST_ENTRIES)
        as (IntrusiveListIndexed.is_list_ring_ix LIST_PAYLOAD LIST_HEAD 1.0R LIST_APPEND(LIST_FRONT, LIST_BACK)));
    _ghost_stmt(IntrusiveListContext.prepare_validation LIST_PAYLOAD LIST_HEAD $(position) LIST_FRONT LIST_BACK);
    list_validate(position);
    _ghost_stmt(IntrusiveListContext.finish_validation LIST_PAYLOAD LIST_HEAD $(position) LIST_FRONT LIST_BACK);
    _ghost_stmt(IntrusiveListOps.position_open LIST_PAYLOAD LIST_HEAD $(position) LIST_FRONT LIST_BACK);
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(position));
    struct list_node *next = position->next;
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(position));
    _ghost_stmt(IntrusiveListOps.position_close LIST_PAYLOAD LIST_HEAD $(position) $(next) LIST_FRONT LIST_BACK);
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold_uninit $(entry));
    entry->prev = position;
    entry->next = next;
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(entry));
    _ghost_stmt(IntrusiveListOps.add_expose_next LIST_PAYLOAD LIST_HEAD $(position) $(next) LIST_FRONT LIST_BACK);
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(next));
    next->prev = entry;
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(next));
    _ghost_stmt(IntrusiveListOps.add_reseat LIST_PAYLOAD LIST_HEAD $(position) $(next) $(entry)
        LIST_DESCRIPTION LIST_FRONT LIST_BACK);
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(position));
    position->next = entry;
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(position));
    _ghost_stmt(IntrusiveListOps.add_close LIST_PAYLOAD LIST_HEAD $(position) $(next) $(entry)
        LIST_DESCRIPTION LIST_FRONT LIST_BACK);
    _ghost_stmt(fold (IntrusiveListContext.insert_after_post LIST_CTX $(entry)));
}

void list_insert_head(_plain struct list_node *head, _plain struct list_node *entry)
{
    _ghost_stmt(unfold (IntrusiveListContext.insert_pre LIST_CTX $(head) $(entry)));
    _ghost_stmt(fold (IntrusiveListContext.insert_after_pre
        (LIST_CUT(LIST_MODEL, $(head), [], LIST_ENTRIES, LIST_DESCRIPTION)) $(head) $(entry)));
    list_insert_after(head, entry);
    _ghost_stmt(unfold (IntrusiveListContext.insert_after_post
        (LIST_CUT(LIST_MODEL, $(head), [], LIST_ENTRIES, LIST_DESCRIPTION)) $(entry)));
    _ghost_stmt(fold (IntrusiveListContext.insert_head_post LIST_CTX $(head) $(entry)));
}

void list_insert_tail(_plain struct list_node *head, _plain struct list_node *entry)
{
    _ghost_stmt(unfold (IntrusiveListContext.insert_pre LIST_CTX $(head) $(entry)));
    _ghost_stmt(IntrusiveListContext.finish_ring LIST_MODEL $(head));
    _ghost_stmt(rewrite (IntrusiveListIndexed.is_list_ring_ix LIST_PAYLOAD $(head) 1.0R LIST_ENTRIES)
        as (IntrusiveListIndexed.is_list_ring_ix LIST_PAYLOAD $(head) 1.0R LIST_APPEND([], LIST_ENTRIES)));
    _ghost_stmt(IntrusiveListContext.prepare_validation LIST_PAYLOAD $(head) $(head) [] LIST_ENTRIES);
    list_validate(head);
    _ghost_stmt(IntrusiveListContext.finish_validation LIST_PAYLOAD $(head) $(head) [] LIST_ENTRIES);
    _ghost_stmt(rewrite (IntrusiveListIndexed.is_list_ring_ix LIST_PAYLOAD $(head) 1.0R LIST_APPEND([], LIST_ENTRIES))
        as (IntrusiveListIndexed.is_list_ring_ix LIST_PAYLOAD $(head) 1.0R LIST_ENTRIES));
    _ghost_stmt(IntrusiveListIndexed.ring_open LIST_PAYLOAD $(head));
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(head));
    struct list_node *tail = head->prev;
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(head));
    _ghost_stmt(IntrusiveListIndexed.ring_close LIST_PAYLOAD $(head));
    _ghost_stmt(IntrusiveListContext.prepare_ring LIST_MODEL $(head));
    _ghost_stmt(FStar.List.Tot.Properties.append_l_nil LIST_ENTRIES);
    _ghost_stmt(fold (IntrusiveListContext.insert_after_pre
        (LIST_CUT(LIST_MODEL, $(head), LIST_ENTRIES, [], LIST_DESCRIPTION)) $(tail) $(entry)));
    list_insert_after(tail, entry);
    _ghost_stmt(unfold (IntrusiveListContext.insert_after_post
        (LIST_CUT(LIST_MODEL, $(head), LIST_ENTRIES, [], LIST_DESCRIPTION)) $(entry)));
    _ghost_stmt(fold (IntrusiveListContext.insert_tail_post LIST_CTX $(head) $(entry)));
}

bool list_remove(_plain struct list_node *entry)
{
    _ghost_stmt(unfold (IntrusiveListContext.remove_pre LIST_CTX $(entry)));
    _ghost_stmt(IntrusiveListContext.finish_ring LIST_MODEL LIST_HEAD);
    _ghost_stmt(FStar.List.Tot.Properties.append_assoc LIST_FRONT [($(entry),LIST_DESCRIPTION)] LIST_BACK);
    _ghost_stmt(IntrusiveListIndexed.last_or_snoc LIST_HEAD LIST_FRONT ($(entry),LIST_DESCRIPTION));
    _ghost_stmt(rewrite (IntrusiveListIndexed.is_list_ring_ix LIST_PAYLOAD LIST_HEAD 1.0R LIST_ENTRIES)
        as (IntrusiveListIndexed.is_list_ring_ix LIST_PAYLOAD LIST_HEAD 1.0R
            LIST_APPEND(LIST_APPEND(LIST_FRONT, [($(entry), LIST_DESCRIPTION)]), LIST_BACK)));
    _ghost_stmt(IntrusiveListContext.prepare_validation LIST_PAYLOAD LIST_HEAD $(entry)
        LIST_APPEND(LIST_FRONT, [($(entry), LIST_DESCRIPTION)]) LIST_BACK);
    list_validate(entry);
    _ghost_stmt(IntrusiveListContext.finish_validation LIST_PAYLOAD LIST_HEAD $(entry)
        LIST_APPEND(LIST_FRONT, [($(entry), LIST_DESCRIPTION)]) LIST_BACK);
    _ghost_stmt(rewrite (IntrusiveListIndexed.is_list_ring_ix LIST_PAYLOAD LIST_HEAD 1.0R
        LIST_APPEND(LIST_APPEND(LIST_FRONT, [($(entry), LIST_DESCRIPTION)]), LIST_BACK))
        as (IntrusiveListIndexed.is_list_ring_ix LIST_PAYLOAD LIST_HEAD 1.0R
            LIST_APPEND(LIST_FRONT, (($(entry), LIST_DESCRIPTION) :: LIST_BACK))));
    _ghost_stmt(IntrusiveListOps.del_open LIST_PAYLOAD LIST_HEAD $(entry)
        LIST_DESCRIPTION LIST_FRONT LIST_BACK);
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(entry));
    struct list_node *previous = entry->prev;
    struct list_node *next = entry->next;
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(entry));
    _ghost_stmt(IntrusiveListOps.del_cut_pin LIST_PAYLOAD LIST_HEAD $(previous) $(next) $(entry)
        LIST_DESCRIPTION LIST_FRONT LIST_BACK);
    _ghost_stmt(IntrusiveListOps.del_expose_prev LIST_PAYLOAD LIST_HEAD $(previous) $(next) $(entry)
        LIST_DESCRIPTION LIST_FRONT LIST_BACK);
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(previous));
    previous->next = next;
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(previous));
    _ghost_stmt(IntrusiveListOps.del_reseat_next LIST_PAYLOAD LIST_HEAD $(previous) $(next) $(entry)
        LIST_DESCRIPTION LIST_FRONT LIST_BACK);
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(next));
    next->prev = previous;
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(next));
    _ghost_stmt(IntrusiveListOps.del_close_next LIST_PAYLOAD LIST_HEAD $(previous) $(next) $(entry)
        LIST_DESCRIPTION LIST_FRONT LIST_BACK);
    return previous == next;
    _ghost_stmt(fold (IntrusiveListContext.remove_post LIST_CTX $(entry) $(return)));
}

_plain struct list_node *list_remove_head(_plain struct list_node *head)
{
    _ghost_stmt(unfold (IntrusiveListContext.remove_head_pre LIST_CTX $(head)));
    _ghost_stmt(IntrusiveListContext.finish_ring LIST_CTX $(head));
    _ghost_stmt(rewrite (IntrusiveListIndexed.is_list_ring_ix LIST_RING_PAYLOAD $(head) 1.0R LIST_RING_ENTRIES)
        as (IntrusiveListIndexed.is_list_ring_ix LIST_RING_PAYLOAD $(head) 1.0R LIST_APPEND([], LIST_RING_ENTRIES)));
    _ghost_stmt(IntrusiveListContext.prepare_validation LIST_RING_PAYLOAD $(head) $(head) [] LIST_RING_ENTRIES);
    list_validate(head);
    _ghost_stmt(IntrusiveListContext.finish_validation LIST_RING_PAYLOAD $(head) $(head) [] LIST_RING_ENTRIES);
    _ghost_stmt(rewrite (IntrusiveListIndexed.is_list_ring_ix LIST_RING_PAYLOAD $(head) 1.0R LIST_APPEND([], LIST_RING_ENTRIES))
        as (IntrusiveListIndexed.is_list_ring_ix LIST_RING_PAYLOAD $(head) 1.0R LIST_RING_ENTRIES));
    _ghost_stmt(IntrusiveListIndexed.ring_open LIST_RING_PAYLOAD $(head));
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(head));
    struct list_node *first = head->next;
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(head));
    _ghost_stmt(IntrusiveListIndexed.ring_close LIST_RING_PAYLOAD $(head));
    _ghost_stmt(IntrusiveListContext.prepare_ring LIST_CTX $(head));
    _ghost_stmt(fold (IntrusiveListContext.remove_pre
        (LIST_CUT(LIST_CTX, $(head), [], (FStar.List.Tot.tl LIST_RING_ENTRIES),
            (snd (FStar.List.Tot.hd LIST_RING_ENTRIES)))) $(first)));
    list_remove(first);
    _ghost_stmt(unfold (IntrusiveListContext.remove_post
        (LIST_CUT(LIST_CTX, $(head), [], (FStar.List.Tot.tl LIST_RING_ENTRIES),
            (snd (FStar.List.Tot.hd LIST_RING_ENTRIES)))) $(first) _));
    _ghost_stmt(rewrite
        (IntrusiveListIndexed.is_list_ring_ix LIST_RING_PAYLOAD $(head) 1.0R
            LIST_APPEND([], FStar.List.Tot.tl LIST_RING_ENTRIES))
        as (IntrusiveListIndexed.is_list_ring_ix LIST_RING_PAYLOAD $(head) 1.0R
            (FStar.List.Tot.tl LIST_RING_ENTRIES)));
    _ghost_stmt(assert exists* (next: IntrusiveListIndexed.lref).
        Pulse.Lib.Reference.pts_to $(first) (IntrusiveListIndexed.mklink next $(head)));
    _ghost_stmt(rewrite
        (IntrusiveListIndexed.is_list_ring_ix LIST_RING_PAYLOAD $(head) 1.0R
            (FStar.List.Tot.tl LIST_RING_ENTRIES) **
        (exists* (next: IntrusiveListIndexed.lref).
            Pulse.Lib.Reference.pts_to $(first) (IntrusiveListIndexed.mklink next $(head))) **
        LIST_RING_PAYLOAD $(first) (snd (FStar.List.Tot.hd LIST_RING_ENTRIES)) **
        pure ($(first) == fst (FStar.List.Tot.hd LIST_RING_ENTRIES)))
        as (IntrusiveListContext.remove_head_post LIST_CTX $(head) $(first)));
    return first;
}

void list_move(_plain struct list_node *source, _plain struct list_node *destination)
{
    _ghost_stmt(unfold (IntrusiveListContext.move_pre LIST_CTX $(source) $(destination)));
    bool empty = list_empty(source);
    _ghost_stmt(unfold (IntrusiveListContext.empty_post LIST_SOURCE $(source) $(empty)));
    _ghost_stmt(IntrusiveListContext.finish_ring LIST_SOURCE $(source));
    if (empty) {
        _ghost_stmt(IntrusiveListOps.move_empty LIST_SOURCE_PAYLOAD $(source) $(destination)
            LIST_SOURCE_ENTRIES LIST_DESTINATION_ENTRIES);
        _ghost_stmt(fold (IntrusiveListContext.move_post LIST_CTX $(source) $(destination)));
        return;
    } else {
        _ghost_stmt(IntrusiveListOps.nonempty_intro LIST_SOURCE_PAYLOAD $(source) LIST_SOURCE_ENTRIES);
    }

    _ghost_stmt(IntrusiveListOps.nonempty_elim LIST_SOURCE_PAYLOAD $(source) LIST_SOURCE_ENTRIES);
    _ghost_stmt(IntrusiveListIndexed.ring_open LIST_SOURCE_PAYLOAD $(source));
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(source));
    struct list_node *first = source->next;
    struct list_node *last = source->prev;
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(source));
    _ghost_stmt(IntrusiveListIndexed.ring_close LIST_SOURCE_PAYLOAD $(source));
    _ghost_stmt(IntrusiveListIndexed.ring_open LIST_SOURCE_PAYLOAD $(destination));
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(destination));
    struct list_node *tail = destination->prev;
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(destination));
    _ghost_stmt(IntrusiveListIndexed.ring_close LIST_SOURCE_PAYLOAD $(destination));
    _ghost_stmt(IntrusiveListOps.move_open LIST_SOURCE_PAYLOAD $(source) $(destination) $(first) $(last) $(tail)
        LIST_SOURCE_ENTRIES LIST_DESTINATION_ENTRIES);
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(tail));
    tail->next = first;
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(tail));
    _ghost_stmt(IntrusiveListOps.move_first LIST_SOURCE_PAYLOAD $(source) $(destination) $(first) $(last) $(tail)
        LIST_SOURCE_ENTRIES LIST_DESTINATION_ENTRIES);
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(first));
    first->prev = tail;
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(first));
    _ghost_stmt(IntrusiveListOps.move_last LIST_SOURCE_PAYLOAD $(source) $(destination) $(first) $(last) $(tail)
        LIST_SOURCE_ENTRIES LIST_DESTINATION_ENTRIES);
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(last));
    last->next = destination;
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(last));
    _ghost_stmt(IntrusiveListOps.move_destination LIST_SOURCE_PAYLOAD $(source) $(destination) $(first) $(last) $(tail)
        LIST_SOURCE_ENTRIES LIST_DESTINATION_ENTRIES);
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(destination));
    destination->prev = last;
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(destination));
    _ghost_stmt(IntrusiveListOps.move_close LIST_SOURCE_PAYLOAD $(source) $(destination) $(first) $(last) $(tail)
        LIST_SOURCE_ENTRIES LIST_DESTINATION_ENTRIES);
    _ghost_stmt(IntrusiveListContext.prepare_init (IntrusiveListContext.make LIST_SOURCE_PAYLOAD []) $(source));
    list_init(source);
    _ghost_stmt(IntrusiveListContext.finish_ring (IntrusiveListContext.make LIST_SOURCE_PAYLOAD []) $(source));
    _ghost_stmt(fold (IntrusiveListContext.move_post LIST_CTX $(source) $(destination)));
}
