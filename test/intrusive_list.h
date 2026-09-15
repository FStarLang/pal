#ifndef INTRUSIVE_LIST_H
#define INTRUSIVE_LIST_H

#include "pal.h"
#include <stdbool.h>

struct list_node {
    struct list_node *next;
    struct list_node *prev;
};

#define containing_record(ptr, type, field) _container_of(ptr, type, field)

void list_init(struct list_node *head);
bool list_empty(const struct list_node *head);

/* Check neighboring links of an initialized sentinel or linked entry. */
void list_validate(const struct list_node *node);

/* Insertions require an entry that is not already linked into a list. */
void list_insert_head(struct list_node *head, struct list_node *entry);
void list_insert_tail(struct list_node *head, struct list_node *entry);
void list_insert_after(struct list_node *position, struct list_node *entry);

/* The list must be nonempty. */
struct list_node *list_remove_head(struct list_node *head);

/* Entry must be linked and must not be the sentinel.
   Returns whether the list becomes empty. Does not clear entry's old links. */
bool list_remove(struct list_node *entry);

/* Append source to destination and empty source.
   The heads must belong to distinct, disjoint lists. */
void list_move(struct list_node *source, struct list_node *destination);

#endif
