#include "pal.h"
#include "list.h"
#include <assert.h>

/* Circular intrusive list operations, inspired by MsQuic's quic_platform.h.
   Nodes and the sentinel are caller-owned; no allocation or freeing occurs. */

void list_init(struct list_node *head)
{
    head->next = head;
    head->prev = head;
}

bool list_empty(const struct list_node *head)
{
    return head->next == head;
}

void list_validate(const struct list_node *node)
{
    assert(node->next->prev == node);
    assert(node->prev->next == node);
}

void list_insert_after(struct list_node *position, struct list_node *entry)
{
    list_validate(position);
    struct list_node *next = position->next;
    entry->prev = position;
    entry->next = next;
    next->prev = entry;
    position->next = entry;
}

void list_insert_head(struct list_node *head, struct list_node *entry)
{
    list_insert_after(head, entry);
}

void list_insert_tail(struct list_node *head, struct list_node *entry)
{
    list_validate(head);
    list_insert_after(head->prev, entry);
}

bool list_remove(struct list_node *entry)
{
    list_validate(entry);
    struct list_node *previous = entry->prev;
    struct list_node *next = entry->next;
    previous->next = next;
    next->prev = previous;
    return previous == next;
}

struct list_node *list_remove_head(struct list_node *head)
{
    list_validate(head);
    struct list_node *first = head->next;
    list_remove(first);
    return first;
}

void list_move(struct list_node *source, struct list_node *destination)
{
    if (list_empty(source)) {
        return;
    }

    struct list_node *first = source->next;
    struct list_node *last = source->prev;
    struct list_node *tail = destination->prev;
    tail->next = first;
    first->prev = tail;
    last->next = destination;
    destination->prev = last;
    list_init(source);
}
