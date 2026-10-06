#include <assert.h>
#include "list.h"
#include "pal.h"

/* Nodes and the sentinel are caller-owned; no allocation or freeing occurs. */
/* Ops proves individual link updates; Validate borrows neighboring links.
   Post-return ghost annotations close the proof before PAL emits the Pulse return. */

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
    _ghost_stmt($unfold-uninit(struct list_node) $(head));
    head->next = head;
    head->prev = head;
#ifndef PALOW
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(head));
#endif
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
#ifndef PALOW
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(head));
#endif
    return head->next == head;
#ifndef PALOW
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(head));
#endif
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
#ifndef PALOW
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(position));
#endif
    struct list_node *next = position->next;
#ifndef PALOW
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(position));
#endif
    _ghost_stmt(IntrusiveListOps.position_close LIST_PAYLOAD LIST_HEAD $(position) $(next) LIST_FRONT LIST_BACK);
    _ghost_stmt($unfold-uninit(struct list_node) $(entry));
    entry->prev = position;
    entry->next = next;
#ifndef PALOW
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(entry));
#endif
    _ghost_stmt(IntrusiveListOps.add_expose_next LIST_PAYLOAD LIST_HEAD $(position) $(next) LIST_FRONT LIST_BACK);
#ifndef PALOW
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(next));
#endif
    next->prev = entry;
#ifndef PALOW
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(next));
#endif
    _ghost_stmt(IntrusiveListOps.add_reseat LIST_PAYLOAD LIST_HEAD $(position) $(next) $(entry)
        LIST_DESCRIPTION LIST_FRONT LIST_BACK);
#ifndef PALOW
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(position));
#endif
    position->next = entry;
#ifndef PALOW
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(position));
#endif
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
#ifndef PALOW
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(head));
#endif
    struct list_node *tail = head->prev;
#ifndef PALOW
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(head));
#endif
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
#ifndef PALOW
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(entry));
#endif
    struct list_node *previous = entry->prev;
    struct list_node *next = entry->next;
#ifndef PALOW
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(entry));
#endif
    _ghost_stmt(IntrusiveListOps.del_cut_pin LIST_PAYLOAD LIST_HEAD $(previous) $(next) $(entry)
        LIST_DESCRIPTION LIST_FRONT LIST_BACK);
    _ghost_stmt(IntrusiveListOps.del_expose_prev LIST_PAYLOAD LIST_HEAD $(previous) $(next) $(entry)
        LIST_DESCRIPTION LIST_FRONT LIST_BACK);
#ifndef PALOW
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(previous));
#endif
    previous->next = next;
#ifndef PALOW
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(previous));
#endif
    _ghost_stmt(IntrusiveListOps.del_reseat_next LIST_PAYLOAD LIST_HEAD $(previous) $(next) $(entry)
        LIST_DESCRIPTION LIST_FRONT LIST_BACK);
#ifndef PALOW
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(next));
#endif
    next->prev = previous;
#ifndef PALOW
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(next));
#endif
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
#ifndef PALOW
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(head));
#endif
    struct list_node *first = head->next;
#ifndef PALOW
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(head));
#endif
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
        IntrusiveListIndexed.lpts_to $(first) (IntrusiveListIndexed.mklink next $(head)));
    _ghost_stmt(rewrite
        (IntrusiveListIndexed.is_list_ring_ix LIST_RING_PAYLOAD $(head) 1.0R
            (FStar.List.Tot.tl LIST_RING_ENTRIES) **
        (exists* (next: IntrusiveListIndexed.lref).
            IntrusiveListIndexed.lpts_to $(first) (IntrusiveListIndexed.mklink next $(head))) **
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
#ifndef PALOW
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(source));
#endif
    struct list_node *first = source->next;
    struct list_node *last = source->prev;
#ifndef PALOW
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(source));
#endif
    _ghost_stmt(IntrusiveListIndexed.ring_close LIST_SOURCE_PAYLOAD $(source));
    _ghost_stmt(IntrusiveListIndexed.ring_open LIST_SOURCE_PAYLOAD $(destination));
#ifndef PALOW
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(destination));
#endif
    struct list_node *tail = destination->prev;
#ifndef PALOW
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(destination));
#endif
    _ghost_stmt(IntrusiveListIndexed.ring_close LIST_SOURCE_PAYLOAD $(destination));
    _ghost_stmt(IntrusiveListOps.move_open LIST_SOURCE_PAYLOAD $(source) $(destination) $(first) $(last) $(tail)
        LIST_SOURCE_ENTRIES LIST_DESTINATION_ENTRIES);
#ifndef PALOW
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(tail));
#endif
    tail->next = first;
#ifndef PALOW
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(tail));
#endif
    _ghost_stmt(IntrusiveListOps.move_first LIST_SOURCE_PAYLOAD $(source) $(destination) $(first) $(last) $(tail)
        LIST_SOURCE_ENTRIES LIST_DESTINATION_ENTRIES);
#ifndef PALOW
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(first));
#endif
    first->prev = tail;
#ifndef PALOW
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(first));
#endif
    _ghost_stmt(IntrusiveListOps.move_last LIST_SOURCE_PAYLOAD $(source) $(destination) $(first) $(last) $(tail)
        LIST_SOURCE_ENTRIES LIST_DESTINATION_ENTRIES);
#ifndef PALOW
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(last));
#endif
    last->next = destination;
#ifndef PALOW
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(last));
#endif
    _ghost_stmt(IntrusiveListOps.move_destination LIST_SOURCE_PAYLOAD $(source) $(destination) $(first) $(last) $(tail)
        LIST_SOURCE_ENTRIES LIST_DESTINATION_ENTRIES);
#ifndef PALOW
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(destination));
#endif
    destination->prev = last;
#ifndef PALOW
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(destination));
#endif
    _ghost_stmt(IntrusiveListOps.move_close LIST_SOURCE_PAYLOAD $(source) $(destination) $(first) $(last) $(tail)
        LIST_SOURCE_ENTRIES LIST_DESTINATION_ENTRIES);
    _ghost_stmt(IntrusiveListContext.prepare_init (IntrusiveListContext.make LIST_SOURCE_PAYLOAD []) $(source));
    list_init(source);
    _ghost_stmt(IntrusiveListContext.finish_ring (IntrusiveListContext.make LIST_SOURCE_PAYLOAD []) $(source));
    _ghost_stmt(fold (IntrusiveListContext.move_post LIST_CTX $(source) $(destination)));
}
