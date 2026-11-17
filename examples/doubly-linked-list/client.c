#include <assert.h>
#include <stddef.h>
#include "dll.h"

/* Indexed integer items: lookup, stable insertion, filtering, and ownership-returning pop. */
/* Assertion operands are evaluated only when assertions are enabled. */
#ifdef C2PULSE
#define ITEMS_ASSERT_ENABLED pal_c_assert_enabled()
#elif defined(NDEBUG)
#define ITEMS_ASSERT_ENABLED 0
#else
#define ITEMS_ASSERT_ENABLED 1
#endif

struct item *items_find(struct list_node *head, int value)
{
    struct list_node *node = head->next;
    while (node != head)
    {
        /* Save the successor before recovering the enclosing item. */
        struct list_node *next = node->next;
        struct item *item = item_from_link(node);
        int current_value = item->value;
        if (current_value == value) {
            return item;
        }
        node = next;
    }
    return NULL;
}

struct item *items_pop_front(struct list_node *head)
{
    bool empty = list_empty(head);
    if (empty) {
        return NULL;
    } else {
        struct list_node *node = list_remove_head(head);
        return item_from_link(node);
    }
}

/* Insert before the first larger item, preserving the order of equal values. */
void items_insert_sorted(struct list_node *head, struct item *item)
{
    /* The new item's value is constant throughout the scan. */
    int new_value = item->value;
    struct list_node *entry = &item->link;
    struct list_node *node = head->next;
    while (node != head)
    {
        struct item *current = item_from_link(node);
        int current_value = current->value;
        if (current_value > new_value) {
            break;
        } else {
            struct list_node *next = node->next;
            node = next;
        }
    }
    bool at_head = node == head;

    if (at_head) {
        list_insert_tail(head, entry);
    } else {
        struct list_node *first = head->next;
        if (node == first) {
            list_insert_head(head, entry);
        } else {
            struct list_node *previous = node->prev;
            list_insert_after(previous, entry);
        }
    }
}

void items_remove_value(struct list_node *head, int value)
{
    struct list_node *node = head->next;
    while (node != head)
    {
        struct list_node *next = node->next;
        struct item *item = item_from_link(node);
        int current_value = item->value;
        if (current_value == value) {
            list_remove(node);
        } else {
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
    bool assertion_empty = false;
    struct item *assertion_item = NULL;

    struct list_node *third_link = &third.link;
    list_init(&source);
    list_init(&destination);
    list_validate(&source);
    list_validate(&destination);
    if (ITEMS_ASSERT_ENABLED) {
        assertion_empty = list_empty(&source);
        assert(assertion_empty);
        assertion_empty = false;
    }
    struct item *removed = items_pop_front(&source);
    assert(removed == NULL);

    items_insert_sorted(&source, &first);
    items_insert_sorted(&source, &second);
    items_insert_sorted(&source, &third);
    list_validate(&source);
    list_validate(third_link);
    if (ITEMS_ASSERT_ENABLED) {
        assertion_item = items_find(&source, 2);
        assert(assertion_item == &third);
        assertion_item = NULL;
    }
    if (ITEMS_ASSERT_ENABLED) {
        assertion_item = items_find(&source, 9);
        assert(assertion_item == NULL);
        assertion_item = NULL;
    }

    list_move(&source, &destination);
    list_validate(&source);
    list_validate(&destination);
    if (ITEMS_ASSERT_ENABLED) {
        assertion_empty = list_empty(&source);
        assert(assertion_empty);
        assertion_empty = false;
    }
    items_insert_sorted(&source, &fourth);
    list_move(&source, &destination);
    list_validate(&source);
    list_validate(&destination);
    if (ITEMS_ASSERT_ENABLED) {
        assertion_empty = list_empty(&source);
        assert(assertion_empty);
        assertion_empty = false;
    }
    list_move(&source, &destination);

    items_remove_value(&destination, 2);
    if (ITEMS_ASSERT_ENABLED) {
        assertion_item = items_find(&destination, 2);
        assert(assertion_item == NULL);
        assertion_item = NULL;
    }
    removed = items_pop_front(&destination);
    assert(removed == &second);
    removed = items_pop_front(&destination);
    assert(removed == &first);
    removed = items_pop_front(&destination);
    assert(removed == &fourth);
    if (ITEMS_ASSERT_ENABLED) {
        assertion_empty = list_empty(&destination);
        assert(assertion_empty);
        assertion_empty = false;
    }
    list_validate(&destination);
    (void)assertion_empty;
    (void)assertion_item;
    (void)removed;
}
