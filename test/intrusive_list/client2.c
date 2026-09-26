#include <assert.h>
#include <limits.h>
#include <stddef.h>
#include "list.h"
#include "pal.h"

/* Indexed resource items: queue operations retain the samples and owned counter.
   Sample processing happens after dequeue, when the caller owns the whole item. */
struct item2 {
    int priority;
    unsigned used;
    unsigned samples[4];
    _plain unsigned *processed;
    struct list_node link;
};

_type(item2_description, IntrusiveListExample2.description)
_type(item2_entries, IntrusiveListExample2.entries)
_type(item2_link, Struct_list_node.struct_list_node)

#ifdef C2PULSE
#define ITEMS2_ASSERT_ENABLED pal_c_assert_enabled()
#elif defined(NDEBUG)
#define ITEMS2_ASSERT_ENABLED 0
#else
#define ITEMS2_ASSERT_ENABLED 1
#endif

_plain struct item2 *items2_find(_plain struct list_node *head, int priority)
    _ghost_arg(item2_entries entries)
    _requires(_inline_pulse(
        IntrusiveListIndexed.is_list_ring_ix IntrusiveListExample2.item_ipl
            $(head) 1.0R (reveal $(entries))))
    _ensures(_inline_pulse(
        IntrusiveListIndexed.is_list_ring_ix IntrusiveListExample2.item_ipl
            $(head) 1.0R (reveal $(entries)) **
        pure ($(return) == IntrusiveListExample2.first_match $(priority) (reveal $(entries)))))
{
    _ghost_stmt(IntrusiveListIndexed.head_open IntrusiveListExample2.item_ipl
        $(head) (reveal $(entries)));
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(head));
    _plain struct list_node *node = head->next;
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(head));
    _ghost_stmt(IntrusiveListItems.find_start IntrusiveListExample2.item_ipl
        (IntrusiveListExample2.matches_priority $(priority)) $(head) $(node) (reveal $(entries)));
    while (node != head)
        _invariant(_live(node))
        _invariant(_inline_pulse(IntrusiveListItems.find_inv IntrusiveListExample2.item_ipl
            (IntrusiveListExample2.matches_priority $(priority))
            $(head) $(node) (reveal $(entries)))) {
        _ghost_stmt(IntrusiveListItems.find_open IntrusiveListExample2.item_ipl
            (IntrusiveListExample2.matches_priority $(priority))
            $(head) $(node) (reveal $(entries)));
        _ghost_stmt(with description. assert IntrusiveListExample2.item_ipl $(node) description);
        _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(node));
        /* The successor is read while the node is still a node: opening the
           payload joins the link back into the item it belongs to, and there
           is no reading `node->next` once it is a field of that. */
        _plain struct list_node *next = node->next;
        _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(node));
        _plain struct item2 *item = containing_record(node, struct item2, link);
        _ghost_stmt(IntrusiveListExample2.value_open $(node) $(item));
        int current_priority = item->priority;
        if (current_priority == priority) {
            _ghost_stmt(IntrusiveListExample2.value_close $(node) $(item));
            _ghost_stmt(IntrusiveListItems.find_found IntrusiveListExample2.item_ipl
                (IntrusiveListExample2.matches_priority $(priority))
                $(head) $(node) (reveal $(entries)) description);
            return item;
        }
        _ghost_stmt(IntrusiveListExample2.value_close $(node) $(item));
        _ghost_stmt(IntrusiveListItems.find_step IntrusiveListExample2.item_ipl
            (IntrusiveListExample2.matches_priority $(priority))
            $(head) $(node) $(next) (reveal $(entries)) description);
        node = next;
    }
    _ghost_stmt(IntrusiveListItems.find_end IntrusiveListExample2.item_ipl
        (IntrusiveListExample2.matches_priority $(priority)) $(head) $(node) (reveal $(entries)));
    return NULL;
}

_plain struct item2 *items2_pop_front(_plain struct list_node *head)
    _ghost_arg(item2_entries entries)
    _requires(_inline_pulse(
        IntrusiveListIndexed.is_list_ring_ix IntrusiveListExample2.item_ipl
            $(head) 1.0R (reveal $(entries))))
    _ensures(_inline_pulse(
        IntrusiveListExample2.pop_post $(head) (reveal $(entries)) $(return)))
{
    _ghost_stmt(IntrusiveListContext.prepare_empty IntrusiveListExample2.item_ipl
        $(head) (reveal $(entries)));
    bool empty = list_empty(head);
    _ghost_stmt(IntrusiveListContext.finish_empty IntrusiveListExample2.item_ipl
        $(head) (reveal $(entries)));
    if (empty) {
        _ghost_stmt(IntrusiveListItems.pop_empty IntrusiveListExample2.item_ipl
            $(head) (reveal $(entries)));
        _ghost_stmt(IntrusiveListExample2.close_pop_empty $(head) (reveal $(entries)));
        return NULL;
    } else {
        _ghost_stmt(IntrusiveListContext.prepare_pop IntrusiveListExample2.item_ipl
            $(head) (reveal $(entries)));
        _plain struct list_node *node = list_remove_head(head);
        _ghost_stmt(IntrusiveListItems.pop_finish IntrusiveListExample2.item_ipl
            $(head) $(node) (reveal $(entries)));
        _ghost_stmt(IntrusiveListExample2.close_pop $(head) $(node) (reveal $(entries)));
        return containing_record(node, struct item2, link);
    }
}

/* Equal priorities retain their enqueue order. */
void items2_insert_sorted(_plain struct list_node *head, _plain struct item2 *item)
    _ghost_arg(item2_entries entries)
    _ghost_arg(item2_description description)
    _requires(_inline_pulse(
        IntrusiveListIndexed.is_list_ring_ix IntrusiveListExample2.item_ipl
            $(head) 1.0R (reveal $(entries)) **
        IntrusiveListExample2.detached $(item) (reveal $(description)) **
        pure (IntrusiveListIndexed.sorted IntrusiveListExample2.priority_le (reveal $(entries)))))
    _ensures(_inline_pulse(
        IntrusiveListIndexed.is_list_ring_ix IntrusiveListExample2.item_ipl
            $(head) 1.0R
            (IntrusiveListIndexed.insert IntrusiveListExample2.priority_le
                (IntrusiveListExample2.node $(item))
                (reveal $(description)) (reveal $(entries))) **
        pure (IntrusiveListIndexed.sorted IntrusiveListExample2.priority_le
            (IntrusiveListIndexed.insert IntrusiveListExample2.priority_le
                (IntrusiveListExample2.node $(item))
                (reveal $(description)) (reveal $(entries))))))
{
    _ghost_stmt(IntrusiveListExample2.priority_order ());
    /* The item's own priority does not change, so it is read once, while the
       item is still whole: from `prepare_item` on, its link belongs to the
       list machinery and the item is no longer an object one can read. */
    _ghost_stmt(IntrusiveListExample2.open_for_insert $(item) (reveal $(description)));
    int new_priority = item->priority;
    _plain struct list_node *entry = &item->link;
    _ghost_stmt(IntrusiveListExample2.prepare_item $(item) $(entry) (reveal $(description)));
    _ghost_stmt(IntrusiveListIndexed.head_open IntrusiveListExample2.item_ipl
        $(head) (reveal $(entries)));
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(head));
    _plain struct list_node *node = head->next;
    _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(head));
    _ghost_stmt(IntrusiveListInsert.start IntrusiveListExample2.item_ipl
        IntrusiveListExample2.priority_le $(head) $(node) $(entry)
        (reveal $(description)) (reveal $(entries)));
    _ghost_stmt(let stopped = Pulse.Lib.GhostReference.alloc (0 = 1));
    while (node != head)
        _invariant(_live(node))
        /* Read before the loop, so the loop has to be told it still holds. */
        _invariant(_inline_pulse(pure ($(new_priority) ==
            (reveal $(description)).IntrusiveListExample2.priority)))
        _invariant(_inline_pulse(live stopped))
        _invariant(_inline_pulse(
            IntrusiveListInsert.inv IntrusiveListExample2.item_ipl
                IntrusiveListExample2.priority_le $(head) $(node) $(entry)
                (reveal $(description)) (reveal $(entries))
                (Pulse.Lib.GhostReference.op_Bang stopped) **
            IntrusiveListExample2.item_ipl $(entry) (reveal $(description)) **
            IntrusiveListIndexed.lpts_to_uninit $(entry)))
        _ensures(_inline_pulse(
            (Pulse.Lib.GhostReference.op_Bang stopped) == (0 = 0) \/
            $(node) == $(head))) {
        _ghost_stmt(IntrusiveListInsert.expose IntrusiveListExample2.item_ipl
            IntrusiveListExample2.priority_le $(head) $(node) $(entry)
            (reveal $(description)) (reveal $(entries)));
        _plain struct item2 *current = containing_record(node, struct item2, link);
        _ghost_stmt(IntrusiveListExample2.value_open $(node) $(current));
        int current_priority = current->priority;
        _ghost_stmt(IntrusiveListExample2.value_close $(node) $(current));
        if (current_priority > new_priority) {
            _ghost_stmt(IntrusiveListInsert.unexpose IntrusiveListExample2.item_ipl
                IntrusiveListExample2.priority_le $(head) $(node) $(entry)
                (reveal $(description)) (reveal $(entries)) (0 = 0));
            _ghost_stmt(Pulse.Lib.GhostReference.write stopped (hide (0 = 0)));
            break;
        } else {
            _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(node));
            _plain struct list_node *next = node->next;
            _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(node));
            _ghost_stmt(IntrusiveListInsert.mid_repack IntrusiveListExample2.item_ipl
                IntrusiveListExample2.priority_le $(head) $(node) $(entry)
                (reveal $(description)) (reveal $(entries)));
            _ghost_stmt(IntrusiveListInsert.step IntrusiveListExample2.item_ipl
                IntrusiveListExample2.priority_le $(head) $(node) $(next) $(entry)
                (reveal $(description)) (reveal $(entries)));
            node = next;
            _ghost_stmt(Pulse.Lib.GhostReference.write stopped (hide (0 = 1)));
        }
    }
    bool at_head = node == head;
    _ghost_stmt(IntrusiveListInsert.settle IntrusiveListExample2.item_ipl
        IntrusiveListExample2.priority_le $(head) $(node) $(entry)
        (reveal $(description)) (reveal $(entries)));
    _ghost_stmt(Pulse.Lib.GhostReference.free stopped);

    if (at_head) {
        _ghost_stmt(IntrusiveListInsert.prepare_tail IntrusiveListExample2.item_ipl
            IntrusiveListExample2.priority_le $(head) $(node) $(entry)
            (reveal $(description)) (reveal $(entries)));
        list_insert_tail(head, entry);
        _ghost_stmt(IntrusiveListInsert.finish_tail IntrusiveListExample2.item_ipl
            IntrusiveListExample2.priority_le $(head) $(entry)
            (reveal $(description)) (reveal $(entries)));
    } else {
        _ghost_stmt(IntrusiveListInsert.head_open IntrusiveListExample2.item_ipl
            IntrusiveListExample2.priority_le $(head) $(node) $(entry)
            (reveal $(description)) (reveal $(entries)));
        _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(head));
        _plain struct list_node *first = head->next;
        _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(head));
        _ghost_stmt(IntrusiveListInsert.head_close IntrusiveListExample2.item_ipl
            IntrusiveListExample2.priority_le $(head) $(node) $(entry)
            (reveal $(description)) (reveal $(entries)));
        if (node == first) {
            _ghost_stmt(IntrusiveListInsert.prepare_head IntrusiveListExample2.item_ipl
                IntrusiveListExample2.priority_le $(head) $(node) $(entry)
                (reveal $(description)) (reveal $(entries)));
            list_insert_head(head, entry);
            _ghost_stmt(IntrusiveListInsert.finish_head IntrusiveListExample2.item_ipl
                IntrusiveListExample2.priority_le $(head) $(entry)
                (reveal $(description)) (reveal $(entries)));
        } else {
            _ghost_stmt(IntrusiveListInsert.position_open IntrusiveListExample2.item_ipl
                IntrusiveListExample2.priority_le $(head) $(node) $(entry)
                (reveal $(description)) (reveal $(entries)));
            _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_unfold $(node));
            _plain struct list_node *previous = node->prev;
            _ghost_stmt(Struct_list_node.struct_list_node__aux_raw_fold $(node));
            _ghost_stmt(IntrusiveListInsert.position_close IntrusiveListExample2.item_ipl
                IntrusiveListExample2.priority_le $(head) $(node) $(previous) $(entry)
                (reveal $(description)) (reveal $(entries)));
            _ghost_stmt(IntrusiveListInsert.prepare_after IntrusiveListExample2.item_ipl
                IntrusiveListExample2.priority_le $(head) $(previous) $(entry)
                (reveal $(description)) (reveal $(entries)));
            list_insert_after(previous, entry);
            _ghost_stmt(IntrusiveListInsert.finish IntrusiveListExample2.item_ipl
                IntrusiveListExample2.priority_le $(head) $(entry)
                (reveal $(description)) (reveal $(entries)));
        }
    }
}

unsigned item2_process_sample(_plain struct item2 *item, unsigned index)
    _ghost_arg(item2_description description)
    _ghost_arg(item2_link link)
    _requires(_inline_pulse(
        IntrusiveListExample2.owned $(item) (reveal $(description)) (reveal $(link)) **
        pure (UInt32.v $(index) < UInt32.v (reveal $(description)).used) **
        pure (UInt32.v (reveal $(description)).count < 4294967295)))
    _ensures(_inline_pulse(
        IntrusiveListExample2.owned $(item)
            (IntrusiveListExample2.processed (reveal $(description))) (reveal $(link)) **
        pure ($(return) == IntrusiveListExample2.sample_at
            (reveal $(description)) (UInt32.v $(index))) **
        pure (UInt32.v (IntrusiveListExample2.processed (reveal $(description))).count ==
            UInt32.v (reveal $(description)).count + 1)))
{
    _ghost_stmt(IntrusiveListExample2.processing_open $(item)
        (reveal $(description)) (reveal $(link)));
    unsigned sample = item->samples[index];
    _plain unsigned *counter = item->processed;
    unsigned before = *counter;
    *counter = before + 1;
    _ghost_stmt(IntrusiveListExample2.processing_close $(item)
        (reveal $(description)) (reveal $(link)));
    _ghost_stmt(IntrusiveListExample2.processed_exact (reveal $(description)));
    return sample;
}

void list_example2(void)
{
    struct list_node head;
    unsigned first_count = 0;
    unsigned second_count = 7;
    unsigned third_count = 3;
    unsigned fourth_count = 0;
    struct item2 first = {
        .priority = 2, .used = 4, .samples = {11, 12, 13, 14}, .processed = &first_count
    };
    struct item2 second = {
        .priority = 1, .used = 0, .samples = {21, 22, 23, 24}, .processed = &second_count
    };
    struct item2 third = {
        .priority = 2, .used = 2, .samples = {31, 32, 33, 34}, .processed = &third_count
    };
    struct item2 fourth = {
        .priority = 4, .used = 4, .samples = {41, 42, 43, 44}, .processed = &fourth_count
    };
    _ghost_stmt(let d_first = IntrusiveListExample2.make 2l 4ul
        (IntrusiveListExample2.samples_of [11ul; 12ul; 13ul; 14ul]) $(&first_count) 0ul);
    _ghost_stmt(let d_second = IntrusiveListExample2.make 1l 0ul
        (IntrusiveListExample2.samples_of [21ul; 22ul; 23ul; 24ul]) $(&second_count) 7ul);
    _ghost_stmt(let d_third = IntrusiveListExample2.make 2l 2ul
        (IntrusiveListExample2.samples_of [31ul; 32ul; 33ul; 34ul]) $(&third_count) 3ul);
    _ghost_stmt(let d_fourth = IntrusiveListExample2.make 4l 4ul
        (IntrusiveListExample2.samples_of [41ul; 42ul; 43ul; 44ul]) $(&fourth_count) 0ul);
    _ghost_stmt(IntrusiveListExample2.capture $(&first) $(&first_count) d_first);
    _ghost_stmt(IntrusiveListExample2.capture $(&second) $(&second_count) d_second);
    _ghost_stmt(IntrusiveListExample2.capture $(&third) $(&third_count) d_third);
    _ghost_stmt(IntrusiveListExample2.capture $(&fourth) $(&fourth_count) d_fourth);
    _ghost_stmt(IntrusiveListExample2.open_detached $(&first) d_first);
    _ghost_stmt(with initial_link. assert IntrusiveListExample2.owned $(&first) d_first initial_link);
    _ghost_stmt(IntrusiveListExample2.resource_roundtrip $(&first) d_first initial_link);
    _ghost_stmt(IntrusiveListExample2.close_detached $(&first) d_first);

    _ghost_stmt(IntrusiveListContext.prepare_init
        (IntrusiveListContext.make IntrusiveListExample2.item_ipl []) $(&head));
    list_init(&head);
    _ghost_stmt(IntrusiveListContext.finish_ring
        (IntrusiveListContext.make IntrusiveListExample2.item_ipl []) $(&head));
    _plain struct item2 *removed = items2_pop_front(&head);
    _ghost_stmt(IntrusiveListExample2.pop_empty_result $(&head) $(removed));
    assert(removed == NULL);

    items2_insert_sorted(&head, &first);
    _ghost_stmt(IntrusiveListOps.indexed_normalize IntrusiveListExample2.item_ipl
        $(&head) [(IntrusiveListExample2.node $(&first), d_first)]);
    items2_insert_sorted(&head, &second);
    _ghost_stmt(IntrusiveListOps.indexed_normalize IntrusiveListExample2.item_ipl
        $(&head) [(IntrusiveListExample2.node $(&second), d_second);
                  (IntrusiveListExample2.node $(&first), d_first)]);
    items2_insert_sorted(&head, &fourth);
    _ghost_stmt(IntrusiveListOps.indexed_normalize IntrusiveListExample2.item_ipl
        $(&head) [(IntrusiveListExample2.node $(&second), d_second);
                  (IntrusiveListExample2.node $(&first), d_first);
                  (IntrusiveListExample2.node $(&fourth), d_fourth)]);
    items2_insert_sorted(&head, &third);
    _ghost_stmt(IntrusiveListOps.indexed_normalize IntrusiveListExample2.item_ipl
        $(&head) [(IntrusiveListExample2.node $(&second), d_second);
                  (IntrusiveListExample2.node $(&first), d_first);
                  (IntrusiveListExample2.node $(&third), d_third);
                  (IntrusiveListExample2.node $(&fourth), d_fourth)]);
    _ghost_stmt(IntrusiveListContext.prepare_validation IntrusiveListExample2.item_ipl
        $(&head) $(&head) []
        [(IntrusiveListExample2.node $(&second), d_second);
         (IntrusiveListExample2.node $(&first), d_first);
         (IntrusiveListExample2.node $(&third), d_third);
         (IntrusiveListExample2.node $(&fourth), d_fourth)]);
    list_validate(&head);
    _ghost_stmt(IntrusiveListContext.finish_validation IntrusiveListExample2.item_ipl
        $(&head) $(&head) []
        [(IntrusiveListExample2.node $(&second), d_second);
         (IntrusiveListExample2.node $(&first), d_first);
         (IntrusiveListExample2.node $(&third), d_third);
         (IntrusiveListExample2.node $(&fourth), d_fourth)]);
    _plain struct item2 *found = NULL;
    if (ITEMS2_ASSERT_ENABLED) {
        found = items2_find(&head, 2);
        assert(found == &first);
        found = NULL;
    }
    if (ITEMS2_ASSERT_ENABLED) {
        found = items2_find(&head, 9);
        assert(found == NULL);
        found = NULL;
    }

    removed = items2_pop_front(&head);
    _ghost_stmt(IntrusiveListExample2.pop_one $(&head) $(&second) $(removed) d_second
        [(IntrusiveListExample2.node $(&first), d_first);
         (IntrusiveListExample2.node $(&third), d_third);
         (IntrusiveListExample2.node $(&fourth), d_fourth)]);
    assert(removed == &second);
    removed = items2_pop_front(&head);
    _ghost_stmt(IntrusiveListExample2.pop_one $(&head) $(&first) $(removed) d_first
        [(IntrusiveListExample2.node $(&third), d_third);
         (IntrusiveListExample2.node $(&fourth), d_fourth)]);
    assert(removed == &first);
    _ghost_stmt(IntrusiveListExample2.open_detached $(&first) d_first);
    unsigned first_sample = item2_process_sample(&first, 0);
    _ghost_stmt(IntrusiveListExample2.close_detached $(&first)
        (IntrusiveListExample2.processed d_first));
    assert(first_sample == 11);
    _ghost_stmt(IntrusiveListExample2.open_detached $(&first)
        (IntrusiveListExample2.processed d_first));
    unsigned last_sample = item2_process_sample(&first, 3);
    _ghost_stmt(let d_processed = IntrusiveListExample2.processed
        (IntrusiveListExample2.processed d_first));
    _ghost_stmt(IntrusiveListExample2.close_detached $(&first) d_processed);
    assert(last_sample == 14);

    /* Re-enqueue after its equal-priority peer, with the updated owned counter. */
    items2_insert_sorted(&head, &first);
    _ghost_stmt(IntrusiveListOps.indexed_normalize IntrusiveListExample2.item_ipl
        $(&head) [(IntrusiveListExample2.node $(&third), d_third);
                  (IntrusiveListExample2.node $(&first), d_processed);
                  (IntrusiveListExample2.node $(&fourth), d_fourth)]);
    if (ITEMS2_ASSERT_ENABLED) {
        found = items2_find(&head, 2);
        assert(found == &third);
        found = NULL;
    }
    removed = items2_pop_front(&head);
    _ghost_stmt(IntrusiveListExample2.pop_one $(&head) $(&third) $(removed) d_third
        [(IntrusiveListExample2.node $(&first), d_processed);
         (IntrusiveListExample2.node $(&fourth), d_fourth)]);
    assert(removed == &third);
    removed = items2_pop_front(&head);
    _ghost_stmt(IntrusiveListExample2.pop_one $(&head) $(&first) $(removed) d_processed
        [(IntrusiveListExample2.node $(&fourth), d_fourth)]);
    assert(removed == &first);
    removed = items2_pop_front(&head);
    _ghost_stmt(IntrusiveListExample2.pop_one $(&head) $(&fourth) $(removed) d_fourth []);
    assert(removed == &fourth);
    removed = items2_pop_front(&head);
    _ghost_stmt(IntrusiveListExample2.pop_empty_result $(&head) $(removed));
    assert(removed == NULL);
    _ghost_stmt(IntrusiveListOps.indexed_release_empty IntrusiveListExample2.item_ipl $(&head));
    _ghost_stmt(IntrusiveListExample2.release_detached $(&first) $(&first_count) d_processed);
    _ghost_stmt(IntrusiveListExample2.release_detached $(&second) $(&second_count) d_second);
    _ghost_stmt(IntrusiveListExample2.release_detached $(&third) $(&third_count) d_third);
    _ghost_stmt(IntrusiveListExample2.release_detached $(&fourth) $(&fourth_count) d_fourth);
    if (ITEMS2_ASSERT_ENABLED) {
        assert(first_count == 2);
        assert(second_count == 7);
        assert(third_count == 3);
        assert(fourth_count == 0);
        assert(first.priority == 2);
        assert(first.used == 4);
        assert(first.samples[0] == 11);
        assert(first.samples[3] == 14);
        assert(first.processed == &first_count);
        assert(second.used == 0);
    }
}
