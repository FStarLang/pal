#include "dll.h"
#include <stdio.h>
#include <stdlib.h>

/* Deliberately independent of assert: these checks also run with NDEBUG. */
#define CHECK(condition)                                                                           \
    do                                                                                             \
    {                                                                                              \
        if (!(condition))                                                                          \
        {                                                                                          \
            fprintf(stderr, "%s:%d: %s\n", __FILE__, __LINE__, #condition);                        \
            exit(EXIT_FAILURE);                                                                    \
        }                                                                                          \
    } while (0)

static void check_order(struct list_node *head, struct item **items, size_t count)
{
    struct list_node *node = head->next;
    struct list_node *previous = head;
    for (size_t i = 0; i < count; ++i)
    {
        CHECK(node == &items[i]->link);
        CHECK(node->prev == previous);
        previous = node;
        node = node->next;
    }
    CHECK(node == head);
    CHECK(head->prev == previous);
    node = head->prev;
    struct list_node *next = head;
    for (size_t i = count; i > 0; --i)
    {
        CHECK(node == &items[i - 1]->link);
        CHECK(node->next == next);
        next = node;
        node = node->prev;
    }
    CHECK(node == head);
    CHECK(head->next == next);
    CHECK(list_empty(head) == (count == 0));
}

int main(void)
{
    list_example();

    struct list_node head, other;
    struct item a = {.value = 2}, b = {.value = 1};
    struct item c = {.value = 2}, d = {.value = 3};
    list_init(&head);
    list_init(&other);
    check_order(&head, NULL, 0);
    CHECK(items_pop_front(&head) == NULL);
    list_move(&other, &head);

    items_insert_sorted(&head, &a);
    items_insert_sorted(&head, &b);
    items_insert_sorted(&head, &c);
    items_insert_sorted(&head, &d);
    struct item *sorted[] = {&b, &a, &c, &d};
    check_order(&head, sorted, 4);
    CHECK(items_find(&head, 2) == &a);
    CHECK(items_find(&head, 99) == NULL);
    list_validate(&head);
    list_validate(&c.link);

    items_remove_value(&head, 99);
    check_order(&head, sorted, 4);
    items_remove_value(&head, 2);
    struct item *survivors[] = {&b, &d};
    check_order(&head, survivors, 2);
    CHECK(items_find(&head, 2) == NULL);
    list_insert_tail(&other, &a.link);
    list_insert_tail(&other, &c.link);
    list_move(&other, &head);
    struct item *appended[] = {&b, &d, &a, &c};
    check_order(&head, appended, 4);
    check_order(&other, NULL, 0);

    CHECK(!list_remove(&d.link));
    CHECK(!list_remove(&c.link));
    CHECK(!list_remove(&b.link));
    struct item *singleton[] = {&a};
    check_order(&head, singleton, 1);
    CHECK(list_remove(&a.link));
    check_order(&head, NULL, 0);

    list_insert_head(&head, &a.link);
    list_insert_after(&a.link, &b.link);
    struct item *pair[] = {&a, &b};
    check_order(&head, pair, 2);
    CHECK(list_remove_head(&head) == &a.link);
    CHECK(items_pop_front(&head) == &b);
    CHECK(items_pop_front(&head) == NULL);
    check_order(&head, NULL, 0);
    puts("DLL: verified client and native forward/backward, stable-order, removal checks passed");
    return 0;
}
