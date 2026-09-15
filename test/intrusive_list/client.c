#include "pal.h"
#include "list.h"
#include <assert.h>
#include <stddef.h>

struct item {
    int value;
    struct list_node link;
};

struct item *items_find(struct list_node *head, int value)
{
    struct list_node *node = head->next;
    while (node != head) {
        struct item *item = containing_record(node, struct item, link);
        if (item->value == value) {
            return item;
        }
        node = node->next;
    }
    return NULL;
}

struct item *items_pop_front(struct list_node *head)
{
    if (list_empty(head)) {
        return NULL;
    }
    struct list_node *node = list_remove_head(head);
    return containing_record(node, struct item, link);
}

/* The list is sorted by value; item is not already linked.
   Like MsQuic's listener registration, insert before the first larger item. */
void items_insert_sorted(struct list_node *head, struct item *item)
{
    struct list_node *node = head->next;
    while (node != head) {
        struct item *current = containing_record(node, struct item, link);
        if (current->value > item->value) {
            break;
        }
        node = node->next;
    }

    if (node == head) {
        list_insert_tail(head, &item->link);
    } else if (node == head->next) {
        list_insert_head(head, &item->link);
    } else {
        list_insert_after(node->prev, &item->link);
    }
}

void items_remove_value(struct list_node *head, int value)
{
    struct list_node *node = head->next;
    while (node != head) {
        struct list_node *next = node->next;
        struct item *item = containing_record(node, struct item, link);
        if (item->value == value) {
            list_remove(node);
        }
        node = next;
    }
}

void list_example(void)
{
    struct list_node source;
    struct list_node destination;
    struct item first = {.value = 3};
    struct item second = {.value = 1};
    struct item third = {.value = 2};
    struct item fourth = {.value = 4};

    list_init(&source);
    list_init(&destination);
    list_validate(&source);
    list_validate(&destination);
    assert(list_empty(&source));
    struct item *removed = items_pop_front(&source);
    assert(removed == NULL);

    items_insert_sorted(&source, &first);
    items_insert_sorted(&source, &second);
    items_insert_sorted(&source, &third);
    list_validate(&source);
    list_validate(&third.link);
    assert(items_find(&source, 2) == &third);
    assert(items_find(&source, 9) == NULL);

    list_move(&source, &destination);
    list_validate(&source);
    list_validate(&destination);
    assert(list_empty(&source));
    items_insert_sorted(&source, &fourth);
    list_move(&source, &destination);
    list_validate(&source);
    list_validate(&destination);
    assert(list_empty(&source));
    list_move(&source, &destination);

    items_remove_value(&destination, 2);
    assert(items_find(&destination, 2) == NULL);
    removed = items_pop_front(&destination);
    assert(removed == &second);
    removed = items_pop_front(&destination);
    assert(removed == &first);
    removed = items_pop_front(&destination);
    assert(removed == &fourth);
    assert(list_empty(&destination));
    list_validate(&destination);
}
