#include <assert.h>
#include <stddef.h>
#include "list.h"
#include "pal.h"

/* Indexed integer items: lookup, stable insertion, filtering, and ownership-returning pop. */
struct item {
    int value;
    struct list_node link;
};

_type(item_entries, IntrusiveListExample.entries)

/* Assertion operands are evaluated only when assertions are enabled. */
#ifdef C2PULSE
#define ITEMS_ASSERT_ENABLED pal_c_assert_enabled()
#elif defined(NDEBUG)
#define ITEMS_ASSERT_ENABLED 0
#else
#define ITEMS_ASSERT_ENABLED 1
#endif

_plain struct item *items_find(_plain struct list_node *head, int value)
    _ghost_arg(item_entries entries)
    _requires(_inline_pulse(
        IntrusiveListIndexed.is_list_ring_ix IntrusiveListExample.item_ipl
            $(head) 1.0R (reveal $(entries))))
    _ensures(_inline_pulse(
        IntrusiveListIndexed.is_list_ring_ix IntrusiveListExample.item_ipl
            $(head) 1.0R (reveal $(entries)) **
        pure ($(return) == IntrusiveListExample.first_match $(value) (reveal $(entries)))))
{
    _ghost_stmt(IntrusiveListIndexed.head_open IntrusiveListExample.item_ipl
        $(head) (reveal $(entries)));
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(head));
    _plain struct list_node *node = head->next;
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(head));
    _ghost_stmt(IntrusiveListItems.find_start IntrusiveListExample.item_ipl
        (IntrusiveListExample.matches_value $(value)) $(head) $(node) (reveal $(entries)));
    while (node != head)
        _invariant(_live(node))
        _invariant(_inline_pulse(IntrusiveListItems.find_inv IntrusiveListExample.item_ipl
            (IntrusiveListExample.matches_value $(value)) $(head) $(node) (reveal $(entries)))) {
        _ghost_stmt(IntrusiveListItems.find_open IntrusiveListExample.item_ipl
            (IntrusiveListExample.matches_value $(value)) $(head) $(node) (reveal $(entries)));
        _ghost_stmt(with description. assert IntrusiveListExample.item_ipl $(node) description);
        _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(node));
        _plain struct item *item = containing_record(node, struct item, link);
        _ghost_stmt(IntrusiveListExample.value_open $(node) $(item));
        int current_value = item->value;
        if (current_value == value) {
            _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(node));
            _ghost_stmt(IntrusiveListExample.value_close $(node) $(item));
            _ghost_stmt(IntrusiveListItems.find_found IntrusiveListExample.item_ipl
                (IntrusiveListExample.matches_value $(value))
                $(head) $(node) (reveal $(entries)) description);
            return item;
        }
        _plain struct list_node *next = node->next;
        _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(node));
        _ghost_stmt(IntrusiveListExample.value_close $(node) $(item));
        _ghost_stmt(IntrusiveListItems.find_step IntrusiveListExample.item_ipl
            (IntrusiveListExample.matches_value $(value))
            $(head) $(node) $(next) (reveal $(entries)) description);
        node = next;
    }
    _ghost_stmt(IntrusiveListItems.find_end IntrusiveListExample.item_ipl
        (IntrusiveListExample.matches_value $(value)) $(head) $(node) (reveal $(entries)));
    return NULL;
}

_plain struct item *items_pop_front(_plain struct list_node *head)
    _ghost_arg(item_entries entries)
    _requires(_inline_pulse(
        IntrusiveListIndexed.is_list_ring_ix IntrusiveListExample.item_ipl
            $(head) 1.0R (reveal $(entries))))
    _ensures(_inline_pulse(
        IntrusiveListExample.pop_post $(head) (reveal $(entries)) $(return)))
{
    _ghost_stmt(IntrusiveListContext.prepare_empty IntrusiveListExample.item_ipl
        $(head) (reveal $(entries)));
    bool empty = list_empty(head);
    _ghost_stmt(IntrusiveListContext.finish_empty IntrusiveListExample.item_ipl
        $(head) (reveal $(entries)));
    if (empty) {
        _ghost_stmt(IntrusiveListItems.pop_empty IntrusiveListExample.item_ipl
            $(head) (reveal $(entries)));
        _ghost_stmt(IntrusiveListExample.close_pop_empty $(head) (reveal $(entries)));
        return NULL;
    } else {
        _ghost_stmt(IntrusiveListContext.prepare_pop IntrusiveListExample.item_ipl
            $(head) (reveal $(entries)));
        _plain struct list_node *node = list_remove_head(head);
        _ghost_stmt(IntrusiveListItems.pop_finish IntrusiveListExample.item_ipl
            $(head) $(node) (reveal $(entries)));
        _ghost_stmt(IntrusiveListExample.close_pop $(head) $(node) (reveal $(entries)));
        return containing_record(node, struct item, link);
    }
}

/* Insert before the first larger item, preserving the order of equal values. */
void items_insert_sorted(_plain struct list_node *head, _plain struct item *item)
    _ghost_arg(item_entries entries)
    _ghost_arg(int description)
    _requires(_inline_pulse(
        IntrusiveListIndexed.is_list_ring_ix IntrusiveListExample.item_ipl
            $(head) 1.0R (reveal $(entries)) **
        (exists* (link: Struct_list_node.struct_list_node).
            Pulse.Lib.Reference.pts_to $(item)
                (IntrusiveListExample.item_record (reveal $(description)) link)) **
        pure (IntrusiveListIndexed.sorted IntrusiveListExample.value_le (reveal $(entries)))))
    _ensures(_inline_pulse(
        IntrusiveListIndexed.is_list_ring_ix IntrusiveListExample.item_ipl
            $(head) 1.0R
            (IntrusiveListIndexed.insert IntrusiveListExample.value_le
                (Struct_item.struct_item__link_1 $(item))
                (reveal $(description)) (reveal $(entries))) **
        pure (IntrusiveListIndexed.sorted IntrusiveListExample.value_le
            (IntrusiveListIndexed.insert IntrusiveListExample.value_le
                (Struct_item.struct_item__link_1 $(item))
                (reveal $(description)) (reveal $(entries))))))
{
    _ghost_stmt(IntrusiveListExample.value_order ());
    _ghost_stmt(Struct_item.struct_item__aux_raw_unfold $(item));
    _plain struct list_node *entry = &item->link;
    _ghost_stmt(IntrusiveListExample.prepare_item $(item) $(entry));
    _ghost_stmt(IntrusiveListIndexed.head_open IntrusiveListExample.item_ipl
        $(head) (reveal $(entries)));
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(head));
    _plain struct list_node *node = head->next;
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(head));
    _ghost_stmt(IntrusiveListInsert.start IntrusiveListExample.item_ipl
        IntrusiveListExample.value_le $(head) $(node) $(entry)
        (reveal $(description)) (reveal $(entries)));
    /* Comparisons keep ghost booleans from expanding through C's stdbool macros. */
    _ghost_stmt(let stopped = Pulse.Lib.GhostReference.alloc (0 = 1));
    while (node != head)
        _invariant(_live(node))
        _invariant(_inline_pulse(live stopped))
        _invariant(_inline_pulse(
            IntrusiveListInsert.inv IntrusiveListExample.item_ipl
                IntrusiveListExample.value_le $(head) $(node) $(entry)
                (reveal $(description)) (reveal $(entries))
                (Pulse.Lib.GhostReference.op_Bang stopped) **
            IntrusiveListExample.item_ipl $(entry) (reveal $(description)) **
            Pulse.Lib.Reference.pts_to_uninit $(entry)))
        _ensures(_inline_pulse(
            (Pulse.Lib.GhostReference.op_Bang stopped) == (0 = 0) \/
            $(node) == $(head))) {
        _ghost_stmt(IntrusiveListInsert.expose IntrusiveListExample.item_ipl
            IntrusiveListExample.value_le $(head) $(node) $(entry)
            (reveal $(description)) (reveal $(entries)));
        _plain struct item *current = containing_record(node, struct item, link);
        _ghost_stmt(IntrusiveListExample.value_open $(node) $(current));
        _ghost_stmt(IntrusiveListExample.value_open $(entry) $(item));
        int current_value = current->value;
        int new_value = item->value;
        _ghost_stmt(IntrusiveListExample.value_close $(node) $(current));
        _ghost_stmt(IntrusiveListExample.value_close $(entry) $(item));
        if (current_value > new_value) {
            _ghost_stmt(IntrusiveListInsert.unexpose IntrusiveListExample.item_ipl
                IntrusiveListExample.value_le $(head) $(node) $(entry)
                (reveal $(description)) (reveal $(entries)) (0 = 0));
            _ghost_stmt(Pulse.Lib.GhostReference.write stopped (hide (0 = 0)));
            break;
        } else {
            _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(node));
            _plain struct list_node *next = node->next;
            _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(node));
            _ghost_stmt(IntrusiveListInsert.mid_repack IntrusiveListExample.item_ipl
                IntrusiveListExample.value_le $(head) $(node) $(entry)
                (reveal $(description)) (reveal $(entries)));
            _ghost_stmt(IntrusiveListInsert.step IntrusiveListExample.item_ipl
                IntrusiveListExample.value_le $(head) $(node) $(next) $(entry)
                (reveal $(description)) (reveal $(entries)));
            node = next;
            _ghost_stmt(Pulse.Lib.GhostReference.write stopped (hide (0 = 1)));
        }
    }
    bool at_head = node == head;
    _ghost_stmt(IntrusiveListInsert.settle IntrusiveListExample.item_ipl
        IntrusiveListExample.value_le $(head) $(node) $(entry)
        (reveal $(description)) (reveal $(entries)));
    _ghost_stmt(Pulse.Lib.GhostReference.free stopped);

    if (at_head) {
        _ghost_stmt(IntrusiveListInsert.prepare_tail IntrusiveListExample.item_ipl
            IntrusiveListExample.value_le $(head) $(node) $(entry)
            (reveal $(description)) (reveal $(entries)));
        list_insert_tail(head, entry);
        _ghost_stmt(IntrusiveListInsert.finish_tail IntrusiveListExample.item_ipl
            IntrusiveListExample.value_le $(head) $(entry)
            (reveal $(description)) (reveal $(entries)));
    } else {
        _ghost_stmt(IntrusiveListInsert.head_open IntrusiveListExample.item_ipl
            IntrusiveListExample.value_le $(head) $(node) $(entry)
            (reveal $(description)) (reveal $(entries)));
        _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(head));
        _plain struct list_node *first = head->next;
        _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(head));
        _ghost_stmt(IntrusiveListInsert.head_close IntrusiveListExample.item_ipl
            IntrusiveListExample.value_le $(head) $(node) $(entry)
            (reveal $(description)) (reveal $(entries)));
        if (node == first) {
            _ghost_stmt(IntrusiveListInsert.prepare_head IntrusiveListExample.item_ipl
                IntrusiveListExample.value_le $(head) $(node) $(entry)
                (reveal $(description)) (reveal $(entries)));
            list_insert_head(head, entry);
            _ghost_stmt(IntrusiveListInsert.finish_head IntrusiveListExample.item_ipl
                IntrusiveListExample.value_le $(head) $(entry)
                (reveal $(description)) (reveal $(entries)));
        } else {
            _ghost_stmt(IntrusiveListInsert.position_open IntrusiveListExample.item_ipl
                IntrusiveListExample.value_le $(head) $(node) $(entry)
                (reveal $(description)) (reveal $(entries)));
            _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(node));
            _plain struct list_node *previous = node->prev;
            _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(node));
            _ghost_stmt(IntrusiveListInsert.position_close IntrusiveListExample.item_ipl
                IntrusiveListExample.value_le $(head) $(node) $(previous) $(entry)
                (reveal $(description)) (reveal $(entries)));
            _ghost_stmt(IntrusiveListInsert.prepare_after IntrusiveListExample.item_ipl
                IntrusiveListExample.value_le $(head) $(previous) $(entry)
                (reveal $(description)) (reveal $(entries)));
            list_insert_after(previous, entry);
            _ghost_stmt(IntrusiveListInsert.finish IntrusiveListExample.item_ipl
                IntrusiveListExample.value_le $(head) $(entry)
                (reveal $(description)) (reveal $(entries)));
        }
    }
}

void items_remove_value(_plain struct list_node *head, int value)
    _ghost_arg(item_entries entries)
    _requires(_inline_pulse(
        IntrusiveListIndexed.is_list_ring_ix IntrusiveListExample.item_ipl
            $(head) 1.0R (reveal $(entries))))
    _ensures(_inline_pulse(
        IntrusiveListIndexed.is_list_ring_ix IntrusiveListExample.item_ipl
            $(head) 1.0R
            (IntrusiveListIndexed.without (IntrusiveListExample.matches_value $(value))
                (reveal $(entries))) **
        IntrusiveListExample.detached
            (IntrusiveListIndexed.matching (IntrusiveListExample.matches_value $(value))
                (reveal $(entries))) **
        pure (IntrusiveListExample.first_match $(value)
            (IntrusiveListIndexed.without (IntrusiveListExample.matches_value $(value))
                (reveal $(entries))) == null)))
{
    _ghost_stmt(IntrusiveListIndexed.head_open IntrusiveListExample.item_ipl
        $(head) (reveal $(entries)));
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(head));
    _plain struct list_node *node = head->next;
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(head));
    _ghost_stmt(IntrusiveListRemove.start IntrusiveListExample.item_ipl
        (IntrusiveListExample.matches_value $(value)) $(head) $(node) (reveal $(entries)));
    while (node != head)
        _invariant(_live(node))
        _invariant(_inline_pulse(IntrusiveListRemove.inv IntrusiveListExample.item_ipl
            (IntrusiveListExample.matches_value $(value)) $(head) $(node) (reveal $(entries)))) {
        _ghost_stmt(IntrusiveListRemove.expose IntrusiveListExample.item_ipl
            (IntrusiveListExample.matches_value $(value)) $(head) $(node) (reveal $(entries)));
        _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(node));
        _plain struct list_node *next = node->next;
        _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(node));
        _plain struct item *item = containing_record(node, struct item, link);
        _ghost_stmt(IntrusiveListExample.value_open $(node) $(item));
        int current_value = item->value;
        _ghost_stmt(IntrusiveListExample.value_close $(node) $(item));
        if (current_value == value) {
            _ghost_stmt(IntrusiveListRemove.drop_prepare IntrusiveListExample.item_ipl
                (IntrusiveListExample.matches_value $(value))
                $(head) $(node) $(next) (reveal $(entries)));
            list_remove(node);
            _ghost_stmt(IntrusiveListRemove.drop_finish IntrusiveListExample.item_ipl
                (IntrusiveListExample.matches_value $(value))
                $(head) $(node) $(next) (reveal $(entries)));
        } else {
            _ghost_stmt(IntrusiveListRemove.keep IntrusiveListExample.item_ipl
                (IntrusiveListExample.matches_value $(value))
                $(head) $(node) $(next) (reveal $(entries)));
        }
        node = next;
    }
    _ghost_stmt(IntrusiveListRemove.finish IntrusiveListExample.item_ipl
        (IntrusiveListExample.matches_value $(value)) $(head) $(node) (reveal $(entries)));
    _ghost_stmt(IntrusiveListExample.close_detached
        (IntrusiveListIndexed.matching (IntrusiveListExample.matches_value $(value))
            (reveal $(entries))));
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
    _plain struct item *assertion_item = NULL;

    _ghost_stmt(Struct_item.struct_item__aux_raw_unfold $(&first) $(first));
    _plain struct list_node *first_link = &first.link;
    _ghost_stmt(IntrusiveListExample.fold_item $(&first));
    _ghost_stmt(Struct_item.struct_item__aux_raw_unfold $(&second) $(second));
    _plain struct list_node *second_link = &second.link;
    _ghost_stmt(IntrusiveListExample.fold_item $(&second));
    _ghost_stmt(Struct_item.struct_item__aux_raw_unfold $(&third) $(third));
    _plain struct list_node *third_link = &third.link;
    _ghost_stmt(IntrusiveListExample.fold_item $(&third));
    _ghost_stmt(Struct_item.struct_item__aux_raw_unfold $(&fourth) $(fourth));
    _plain struct list_node *fourth_link = &fourth.link;
    _ghost_stmt(IntrusiveListExample.fold_item $(&fourth));
    _ghost_stmt(IntrusiveListContext.prepare_init
        (IntrusiveListContext.make IntrusiveListExample.item_ipl []) $(&source));
    list_init(&source);
    _ghost_stmt(IntrusiveListContext.finish_ring
        (IntrusiveListContext.make IntrusiveListExample.item_ipl []) $(&source));
    _ghost_stmt(IntrusiveListContext.prepare_init
        (IntrusiveListContext.make IntrusiveListExample.item_ipl []) $(&destination));
    list_init(&destination);
    _ghost_stmt(IntrusiveListContext.finish_ring
        (IntrusiveListContext.make IntrusiveListExample.item_ipl []) $(&destination));
    _ghost_stmt(IntrusiveListContext.prepare_validation IntrusiveListExample.item_ipl
        $(&source) $(&source) [] []);
    list_validate(&source);
    _ghost_stmt(IntrusiveListContext.finish_validation IntrusiveListExample.item_ipl
        $(&source) $(&source) [] []);
    _ghost_stmt(IntrusiveListContext.prepare_validation IntrusiveListExample.item_ipl
        $(&destination) $(&destination) [] []);
    list_validate(&destination);
    _ghost_stmt(IntrusiveListContext.finish_validation IntrusiveListExample.item_ipl
        $(&destination) $(&destination) [] []);
    _ghost_stmt(IntrusiveListOps.indexed_normalize IntrusiveListExample.item_ipl $(&source) []);
    _ghost_stmt(IntrusiveListOps.indexed_normalize IntrusiveListExample.item_ipl $(&destination) []);
    if (ITEMS_ASSERT_ENABLED) {
        _ghost_stmt(IntrusiveListContext.prepare_empty IntrusiveListExample.item_ipl $(&source) []);
        assertion_empty = list_empty(&source);
        _ghost_stmt(IntrusiveListContext.finish_empty IntrusiveListExample.item_ipl $(&source) []);
        assert(assertion_empty);
        assertion_empty = false;
    }
    _plain struct item *removed = items_pop_front(&source);
    _ghost_stmt(IntrusiveListExample.pop_empty_result $(&source) $(removed));
    assert(removed == NULL);

    items_insert_sorted(&source, &first);
    items_insert_sorted(&source, &second);
    items_insert_sorted(&source, &third);
    _ghost_stmt(IntrusiveListContext.prepare_validation IntrusiveListExample.item_ipl
        $(&source) $(&source) []
        [($(second_link), 1l); ($(third_link), 2l); ($(first_link), 3l)]);
    list_validate(&source);
    _ghost_stmt(IntrusiveListContext.finish_validation IntrusiveListExample.item_ipl
        $(&source) $(&source) []
        [($(second_link), 1l); ($(third_link), 2l); ($(first_link), 3l)]);
    _ghost_stmt(IntrusiveListContext.prepare_validation IntrusiveListExample.item_ipl
        $(&source) $(third_link) [($(second_link), 1l); ($(third_link), 2l)]
        [($(first_link), 3l)]);
    list_validate(third_link);
    _ghost_stmt(IntrusiveListContext.finish_validation IntrusiveListExample.item_ipl
        $(&source) $(third_link) [($(second_link), 1l); ($(third_link), 2l)]
        [($(first_link), 3l)]);
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

    _ghost_stmt(IntrusiveListContext.prepare_move IntrusiveListExample.item_ipl
        $(&source) $(&destination)
        [($(second_link), 1l); ($(third_link), 2l); ($(first_link), 3l)] []);
    list_move(&source, &destination);
    _ghost_stmt(IntrusiveListContext.finish_move IntrusiveListExample.item_ipl
        $(&source) $(&destination)
        [($(second_link), 1l); ($(third_link), 2l); ($(first_link), 3l)] []);
    _ghost_stmt(IntrusiveListContext.prepare_validation IntrusiveListExample.item_ipl
        $(&source) $(&source) [] []);
    list_validate(&source);
    _ghost_stmt(IntrusiveListContext.finish_validation IntrusiveListExample.item_ipl
        $(&source) $(&source) [] []);
    _ghost_stmt(IntrusiveListContext.prepare_validation IntrusiveListExample.item_ipl
        $(&destination) $(&destination) []
        [($(second_link), 1l); ($(third_link), 2l); ($(first_link), 3l)]);
    list_validate(&destination);
    _ghost_stmt(IntrusiveListContext.finish_validation IntrusiveListExample.item_ipl
        $(&destination) $(&destination) []
        [($(second_link), 1l); ($(third_link), 2l); ($(first_link), 3l)]);
    if (ITEMS_ASSERT_ENABLED) {
        _ghost_stmt(IntrusiveListContext.prepare_empty IntrusiveListExample.item_ipl $(&source) []);
        assertion_empty = list_empty(&source);
        _ghost_stmt(IntrusiveListContext.finish_empty IntrusiveListExample.item_ipl $(&source) []);
        assert(assertion_empty);
        assertion_empty = false;
    }
    items_insert_sorted(&source, &fourth);
    _ghost_stmt(IntrusiveListContext.prepare_move IntrusiveListExample.item_ipl
        $(&source) $(&destination) [($(fourth_link), 4l)]
        [($(second_link), 1l); ($(third_link), 2l); ($(first_link), 3l)]);
    list_move(&source, &destination);
    _ghost_stmt(IntrusiveListContext.finish_move IntrusiveListExample.item_ipl
        $(&source) $(&destination) [($(fourth_link), 4l)]
        [($(second_link), 1l); ($(third_link), 2l); ($(first_link), 3l)]);
    _ghost_stmt(IntrusiveListContext.prepare_validation IntrusiveListExample.item_ipl
        $(&source) $(&source) [] []);
    list_validate(&source);
    _ghost_stmt(IntrusiveListContext.finish_validation IntrusiveListExample.item_ipl
        $(&source) $(&source) [] []);
    _ghost_stmt(IntrusiveListContext.prepare_validation IntrusiveListExample.item_ipl
        $(&destination) $(&destination) []
        [($(second_link), 1l); ($(third_link), 2l); ($(first_link), 3l); ($(fourth_link), 4l)]);
    list_validate(&destination);
    _ghost_stmt(IntrusiveListContext.finish_validation IntrusiveListExample.item_ipl
        $(&destination) $(&destination) []
        [($(second_link), 1l); ($(third_link), 2l); ($(first_link), 3l); ($(fourth_link), 4l)]);
    if (ITEMS_ASSERT_ENABLED) {
        _ghost_stmt(IntrusiveListContext.prepare_empty IntrusiveListExample.item_ipl $(&source) []);
        assertion_empty = list_empty(&source);
        _ghost_stmt(IntrusiveListContext.finish_empty IntrusiveListExample.item_ipl $(&source) []);
        assert(assertion_empty);
        assertion_empty = false;
    }
    _ghost_stmt(IntrusiveListContext.prepare_move IntrusiveListExample.item_ipl
        $(&source) $(&destination) []
        [($(second_link), 1l); ($(third_link), 2l); ($(first_link), 3l); ($(fourth_link), 4l)]);
    list_move(&source, &destination);
    _ghost_stmt(IntrusiveListContext.finish_move IntrusiveListExample.item_ipl
        $(&source) $(&destination) []
        [($(second_link), 1l); ($(third_link), 2l); ($(first_link), 3l); ($(fourth_link), 4l)]);

    items_remove_value(&destination, 2);
    _ghost_stmt(IntrusiveListExample.detached_one $(&third) 2l);
    _ghost_stmt(IntrusiveListOps.indexed_normalize IntrusiveListExample.item_ipl
        $(&destination) [($(second_link), 1l); ($(first_link), 3l); ($(fourth_link), 4l)]);
    if (ITEMS_ASSERT_ENABLED) {
        assertion_item = items_find(&destination, 2);
        assert(assertion_item == NULL);
        assertion_item = NULL;
    }
    removed = items_pop_front(&destination);
    _ghost_stmt(IntrusiveListExample.pop_one $(&destination) $(&second) $(removed) 1l
        [($(first_link), 3l); ($(fourth_link), 4l)]);
    assert(removed == &second);
    removed = items_pop_front(&destination);
    _ghost_stmt(IntrusiveListExample.pop_one $(&destination) $(&first) $(removed) 3l
        [($(fourth_link), 4l)]);
    assert(removed == &first);
    removed = items_pop_front(&destination);
    _ghost_stmt(IntrusiveListExample.pop_one $(&destination) $(&fourth) $(removed) 4l []);
    assert(removed == &fourth);
    if (ITEMS_ASSERT_ENABLED) {
        _ghost_stmt(IntrusiveListContext.prepare_empty IntrusiveListExample.item_ipl $(&destination) []);
        assertion_empty = list_empty(&destination);
        _ghost_stmt(IntrusiveListContext.finish_empty IntrusiveListExample.item_ipl $(&destination) []);
        assert(assertion_empty);
        assertion_empty = false;
    }
    _ghost_stmt(IntrusiveListContext.prepare_validation IntrusiveListExample.item_ipl
        $(&destination) $(&destination) [] []);
    list_validate(&destination);
    _ghost_stmt(IntrusiveListContext.finish_validation IntrusiveListExample.item_ipl
        $(&destination) $(&destination) [] []);
    _ghost_stmt(IntrusiveListOps.indexed_release_empty IntrusiveListExample.item_ipl $(&source));
    _ghost_stmt(IntrusiveListOps.indexed_release_empty IntrusiveListExample.item_ipl $(&destination));
}
