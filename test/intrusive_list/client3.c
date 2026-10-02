#include <assert.h>
#include <stddef.h>
#include <stdbool.h>
#include "list.h"
#include "pal.h"

/* The unary queue payload requires ready=true for every linked item.
   The unit adapters below hide indexed transport; dequeue clears the flag. */
struct item3 {
    bool ready;
    struct list_node link;
};

_type(items3_payload, IntrusiveList.payload)
_type(items3_nodes, list IntrusiveList.lref)

#ifdef C2PULSE
#define ITEMS3_ASSERT_ENABLED pal_c_assert_enabled()
#elif defined(NDEBUG)
#define ITEMS3_ASSERT_ENABLED 0
#else
#define ITEMS3_ASSERT_ENABLED 1
#endif

static void items3_unit_init(_plain struct list_node *head)
    _ghost_arg(items3_payload p)
    _requires(_inline_pulse(IntrusiveList.init_pre (reveal $(p)) $(head)))
    _ensures(_inline_pulse(IntrusiveList.is_list_ring_with (reveal $(p)) $(head) 1.0R []))
{
    _ghost_stmt(IntrusiveList.init_open (reveal $(p)) $(head));
    list_init(head);
    _ghost_stmt(IntrusiveList.init_close (reveal $(p)) $(head));
}

static bool items3_unit_empty(_plain struct list_node *head)
    _ghost_arg(items3_payload p)
    _ghost_arg(items3_nodes nodes)
    _requires(_inline_pulse(
        IntrusiveList.is_list_ring_with (reveal $(p)) $(head) 1.0R (reveal $(nodes))))
    _ensures(_inline_pulse(
        IntrusiveList.is_list_ring_with (reveal $(p)) $(head) 1.0R (reveal $(nodes)) **
        pure ($(return) <==> (reveal $(nodes) == []))))
{
    _ghost_stmt(IntrusiveList.empty_open (reveal $(p)) $(head) (reveal $(nodes)));
    bool result = list_empty(head);
    _ghost_stmt(IntrusiveList.empty_close (reveal $(p)) $(head) (reveal $(nodes)));
    return result;
}

static void items3_unit_validate(_plain struct list_node *head)
    _ghost_arg(items3_payload p)
    _ghost_arg(items3_nodes nodes)
    _requires(_inline_pulse(
        IntrusiveList.is_list_ring_with (reveal $(p)) $(head) 1.0R (reveal $(nodes))))
    _ensures(_inline_pulse(
        IntrusiveList.is_list_ring_with (reveal $(p)) $(head) 1.0R (reveal $(nodes))))
{
    _ghost_stmt(IntrusiveList.validate_head_open (reveal $(p)) $(head) (reveal $(nodes)));
    list_validate(head);
    _ghost_stmt(IntrusiveList.validate_head_close (reveal $(p)) $(head) (reveal $(nodes)));
}

static void items3_unit_insert_tail(_plain struct list_node *head,
                                   _plain struct list_node *entry)
    _ghost_arg(items3_payload p)
    _ghost_arg(items3_nodes nodes)
    _requires(_inline_pulse(
        IntrusiveList.tail_pre (reveal $(p)) $(head) $(entry) (reveal $(nodes))))
    _ensures(_inline_pulse(
        IntrusiveList.is_list_ring_with (reveal $(p)) $(head) 1.0R
            (FStar.List.Tot.append (reveal $(nodes)) [$(entry)])))
{
    _ghost_stmt(IntrusiveList.tail_open (reveal $(p)) $(head) $(entry) (reveal $(nodes)));
    list_insert_tail(head, entry);
    _ghost_stmt(IntrusiveList.tail_close (reveal $(p)) $(head) $(entry) (reveal $(nodes)));
}

static _plain struct list_node *items3_unit_remove_head(_plain struct list_node *head)
    _ghost_arg(items3_payload p)
    _ghost_arg(items3_nodes nodes)
    _requires(_inline_pulse(
        IntrusiveList.is_list_ring_with (reveal $(p)) $(head) 1.0R (reveal $(nodes)) **
        pure (reveal $(nodes) =!= [])))
    _ensures(_inline_pulse(
        IntrusiveList.pop_post (reveal $(p)) $(head) (reveal $(nodes)) $(return)))
{
    _ghost_stmt(IntrusiveList.pop_open (reveal $(p)) $(head) (reveal $(nodes)));
    _plain struct list_node *result = list_remove_head(head);
    _ghost_stmt(IntrusiveList.pop_close (reveal $(p)) $(head) $(result) (reveal $(nodes)));
    return result;
}

static void items3_unit_move(_plain struct list_node *source,
                            _plain struct list_node *destination)
    _ghost_arg(items3_payload p)
    _ghost_arg(items3_nodes source_nodes)
    _ghost_arg(items3_nodes destination_nodes)
    _requires(_inline_pulse(
        IntrusiveList.is_list_ring_with (reveal $(p)) $(source) 1.0R (reveal $(source_nodes)) **
        IntrusiveList.is_list_ring_with (reveal $(p)) $(destination) 1.0R
            (reveal $(destination_nodes))))
    _ensures(_inline_pulse(
        IntrusiveList.is_list_ring_with (reveal $(p)) $(source) 1.0R [] **
        IntrusiveList.is_list_ring_with (reveal $(p)) $(destination) 1.0R
            (FStar.List.Tot.append (reveal $(destination_nodes)) (reveal $(source_nodes)))))
{
    _ghost_stmt(IntrusiveList.move_open (reveal $(p)) $(source) $(destination)
        (reveal $(source_nodes)) (reveal $(destination_nodes)));
    list_move(source, destination);
    _ghost_stmt(IntrusiveList.move_close (reveal $(p)) $(source) $(destination)
        (reveal $(source_nodes)) (reveal $(destination_nodes)));
}

void items3_enqueue(_plain struct list_node *head, _plain struct item3 *item)
    _ghost_arg(items3_nodes nodes)
    _requires(_inline_pulse(
        IntrusiveList.is_list_ring_with IntrusiveListExample3.payload
            $(head) 1.0R (reveal $(nodes)) **
        (exists* (v: Struct_item3.struct_item3). IntrusiveListExample3.item_pts_to $(item) v)))
    _ensures(_inline_pulse(
        IntrusiveList.is_list_ring_with IntrusiveListExample3.payload $(head) 1.0R
            (FStar.List.Tot.append (reveal $(nodes)) [IntrusiveListExample3.item_link $(item)])))
{
    _ghost_stmt(IntrusiveListExample3.open_item $(item));
    item->ready = true;
    _plain struct list_node *entry = &item->link;
    _ghost_stmt(IntrusiveListExample3.prepare_enqueue $(item) $(entry));
    _ghost_stmt(IntrusiveList.prepare_tail IntrusiveListExample3.payload
        $(head) $(entry) (reveal $(nodes)));
    items3_unit_insert_tail(head, entry);
    _ghost_stmt(IntrusiveListExample3.enqueue_finish $(head) $(item) $(entry) (reveal $(nodes)));
}

_plain struct item3 *items3_dequeue(_plain struct list_node *head)
    _ghost_arg(items3_nodes nodes)
    _requires(_inline_pulse(
        IntrusiveList.is_list_ring_with IntrusiveListExample3.payload
            $(head) 1.0R (reveal $(nodes))))
    _ensures(_inline_pulse(
        IntrusiveListExample3.dequeue_post $(head) (reveal $(nodes)) $(return)))
{
    bool empty = items3_unit_empty(head);
    if (empty) {
        _ghost_stmt(IntrusiveListExample3.pop_empty $(head) (reveal $(nodes)));
        return NULL;
    } else {
        _plain struct list_node *node = items3_unit_remove_head(head);
        _ghost_stmt(IntrusiveListExample3.pop_open $(head) $(node) (reveal $(nodes)));
        _plain struct item3 *item = containing_record(node, struct item3, link);
        _ghost_stmt(IntrusiveListExample3.ready_open $(node) $(item));
        assert(item->ready);
        item->ready = false;
        _ghost_stmt(IntrusiveListExample3.close_dequeue
            $(head) $(node) $(item) (reveal $(nodes)));
        return item;
    }
}

void items3_append(_plain struct list_node *source, _plain struct list_node *destination)
    _ghost_arg(items3_nodes source_nodes)
    _ghost_arg(items3_nodes destination_nodes)
    _requires(_inline_pulse(
        IntrusiveList.is_list_ring_with IntrusiveListExample3.payload
            $(source) 1.0R (reveal $(source_nodes)) **
        IntrusiveList.is_list_ring_with IntrusiveListExample3.payload
            $(destination) 1.0R (reveal $(destination_nodes))))
    _ensures(_inline_pulse(
        IntrusiveList.is_list_ring_with IntrusiveListExample3.payload $(source) 1.0R [] **
        IntrusiveList.is_list_ring_with IntrusiveListExample3.payload $(destination) 1.0R
            (FStar.List.Tot.append (reveal $(destination_nodes)) (reveal $(source_nodes)))))
{
    items3_unit_move(source, destination);
}

void list_example3(void)
{
    struct list_node source;
    struct list_node destination;
    struct item3 first = {.ready = false};
    struct item3 second = {.ready = false};
    struct item3 third = {.ready = false};
    bool assertion_empty = false;
    _plain struct item3 *removed = NULL;

    _ghost_stmt(Struct_item3.struct_item3__aux_raw_unfold $(&first) $(first));
    _plain struct list_node *first_link = &first.link;
    _ghost_stmt(IntrusiveListExample3.fold_item $(&first));
    _ghost_stmt(Struct_item3.struct_item3__aux_raw_unfold $(&second) $(second));
    _plain struct list_node *second_link = &second.link;
    _ghost_stmt(IntrusiveListExample3.fold_item $(&second));
    _ghost_stmt(Struct_item3.struct_item3__aux_raw_unfold $(&third) $(third));
    _plain struct list_node *third_link = &third.link;
    _ghost_stmt(IntrusiveListExample3.fold_item $(&third));

    _ghost_stmt(IntrusiveList.prepare_init IntrusiveListExample3.payload $(&source));
    items3_unit_init(&source);
    _ghost_stmt(IntrusiveList.prepare_init IntrusiveListExample3.payload $(&destination));
    items3_unit_init(&destination);
    items3_unit_validate(&source);
    items3_unit_validate(&destination);
    if (ITEMS3_ASSERT_ENABLED) {
        assertion_empty = items3_unit_empty(&source);
        assert(assertion_empty);
        assertion_empty = false;
    }
    removed = items3_dequeue(&source);
    _ghost_stmt(IntrusiveListExample3.pop_empty_result $(&source) $(removed));
    assert(removed == NULL);
    items3_append(&source, &destination);

    items3_enqueue(&source, &first);
    items3_enqueue(&source, &second);
    items3_unit_validate(&source);
    if (ITEMS3_ASSERT_ENABLED) {
        assertion_empty = items3_unit_empty(&source);
        assert(!assertion_empty);
        assertion_empty = false;
    }
    removed = items3_dequeue(&source);
    _ghost_stmt(IntrusiveListExample3.pop_one
        $(&source) $(&first) $(removed) [$(second_link)]);
    assert(removed == &first);
    _ghost_stmt(IntrusiveListExample3.open_item $(&first));
    assert(!first.ready);
    _ghost_stmt(IntrusiveListExample3.fold_item $(&first));
    items3_enqueue(&source, &first);

    items3_append(&source, &destination);
    items3_unit_validate(&source);
    items3_unit_validate(&destination);

    items3_enqueue(&source, &third);
    items3_append(&source, &destination);
    items3_append(&source, &destination);
    items3_unit_validate(&destination);
    if (ITEMS3_ASSERT_ENABLED) {
        assertion_empty = items3_unit_empty(&source);
        assert(assertion_empty);
        assertion_empty = false;
    }

    removed = items3_dequeue(&destination);
    _ghost_stmt(IntrusiveListExample3.pop_one
        $(&destination) $(&second) $(removed) [$(first_link); $(third_link)]);
    assert(removed == &second);
    _ghost_stmt(IntrusiveListExample3.open_item $(&second));
    assert(!second.ready);
    _ghost_stmt(IntrusiveListExample3.fold_item $(&second));

    removed = items3_dequeue(&destination);
    _ghost_stmt(IntrusiveListExample3.pop_one
        $(&destination) $(&first) $(removed) [$(third_link)]);
    assert(removed == &first);
    _ghost_stmt(IntrusiveListExample3.open_item $(&first));
    assert(!first.ready);
    _ghost_stmt(IntrusiveListExample3.fold_item $(&first));

    removed = items3_dequeue(&destination);
    _ghost_stmt(IntrusiveListExample3.pop_one $(&destination) $(&third) $(removed) []);
    assert(removed == &third);
    _ghost_stmt(IntrusiveListExample3.open_item $(&third));
    assert(!third.ready);
    _ghost_stmt(IntrusiveListExample3.fold_item $(&third));

    removed = items3_dequeue(&destination);
    _ghost_stmt(IntrusiveListExample3.pop_empty_result $(&destination) $(removed));
    assert(removed == NULL);
    if (ITEMS3_ASSERT_ENABLED) {
        assertion_empty = items3_unit_empty(&destination);
        assert(assertion_empty);
        assertion_empty = false;
    }
    items3_unit_validate(&source);
    items3_unit_validate(&destination);
    _ghost_stmt(IntrusiveList.release_empty IntrusiveListExample3.payload $(&source));
    _ghost_stmt(IntrusiveList.release_empty IntrusiveListExample3.payload $(&destination));
}
