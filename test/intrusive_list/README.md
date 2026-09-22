# Verified intrusive lists

This test verifies a circular doubly linked list and three clients with different
payloads. The C implementation manipulates embedded links; PAL annotations and
the Pulse helpers describe the links, element order, and ownership of the
enclosing objects and their resources.

## C implementation

[`intrusive_list.c`](intrusive_list.c) implements the operations declared in
[`../intrusive_list.h`](../intrusive_list.h), reached through the `list.h` symlink.
An empty sentinel points to itself in both directions. Each member embeds a
`struct list_node`; `containing_record` recovers the enclosing object even when
the link is not its first field.

| Operation | Verified behavior |
|---|---|
| `list_init` | Initializes caller-owned sentinel storage as an empty ring. |
| `list_empty` | Preserves the ring and reports exactly whether it is empty. |
| `list_validate` | Checks neighboring links of a sentinel or member and preserves the ring. |
| `list_insert_after` | Inserts a detached entry at the specified split of the sequence. |
| `list_insert_head` | Prepends an entry. |
| `list_insert_tail` | Appends an entry. |
| `list_remove` | Removes the selected member, returns its link and payload ownership, and reports whether the ring becomes empty. |
| `list_remove_head` | Removes the first member of a nonempty ring and returns its ownership. |
| `list_move` | Appends source entries after destination entries and leaves the source empty. |

The sentinel and elements are caller-owned; these operations allocate or free
neither. Insertion requires detached storage and its payload. Removal does not
clear the detached entry's old links. Moving lists requires disjoint ring
ownership and the same payload model.

All guarantees are under the annotated preconditions. These are sequential
ownership proofs, not a concurrent-list implementation. Ghost statements have
no native runtime effect. Some occur after a C `return`: PAL uses them to close
the proof before emitting the corresponding Pulse return.

## Ownership model and helper files

The foundation is [`IntrusiveListIndexed.fst`](helpers/IntrusiveListIndexed.fst):

```fstar
ipayload a = lref -> a -> slprop
entries a = list (lref & a)

is_list_ring_ix p head permission entries
```

Each `(node, description)` entry owns its link storage and
`p node description`. The sentinel owns links but no member payload.
Descriptions can be integers, structured records, lists, or other types;
structural proofs do not inspect the payload.

[`IntrusiveListContext.fst`](helpers/IntrusiveListContext.fst) is a C annotation
adapter, not another list model. Its erased records package a description type,
payload predicate, and typed entries into named ghost types PAL can accept.
Operation-specific records also carry insertion descriptions or sequence cuts.
For example, `Context.ring ctx head` wraps
`Indexed.is_list_ring_ix ctx.resource head 1.0R ctx.entries`.
F* helpers can still take the predicate and entries directly.

[`IntrusiveList.fst`](helpers/IntrusiveList.fst) derives the nonindexed API by
setting the description type to `unit` and mapping nodes to `(node, ())`.
It includes wrappers checking all nine indexed C contracts at this specialization,
plus proof adapters for client3's C-facing unit wrappers. A unary payload can
still specify field values and own resources; it simply has no separate
per-entry description.

| Helper | Responsibility |
|---|---|
| [`IntrusiveListIndexed`](helpers/IntrusiveListIndexed.fst) | Recursive indexed segments/rings, splitting and rejoining, cursors, payload factoring, and pure sequence specifications. |
| [`IntrusiveListOps`](helpers/IntrusiveListOps.fst) | Intermediate ownership states between individual pointer assignments during insertion, removal, and moving lists. |
| [`IntrusiveListValidate`](helpers/IntrusiveListValidate.fst) | Fractional borrowing of neighboring links, including empty/singleton alias cases, followed by restoration using the same witness. Payloads are framed, not duplicated. |
| [`IntrusiveListContext`](helpers/IntrusiveListContext.fst) | Erased C ghost records, operation contracts, and preparation/completion adapters. |
| [`IntrusiveListItems`](helpers/IntrusiveListItems.fst) | Generic first-match traversal and ownership-returning pop; no concrete `struct item` knowledge. |
| [`IntrusiveListInsert`](helpers/IntrusiveListInsert.fst) | Generic stable sorted-insertion scan and its connection to the C insertion contracts. |
| [`IntrusiveListRemove`](helpers/IntrusiveListRemove.fst) | Generic order-preserving filtering with ownership of every removed node and payload. |
| [`IntrusiveListExample`](helpers/IntrusiveListExample.fst) | Integer-item ownership, comparisons, container recovery, and additional generic instantiations. |
| [`IntrusiveListExample2`](helpers/IntrusiveListExample2.fst) | Structured descriptions and ownership of inline samples and an external counter. |
| [`IntrusiveListExample3`](helpers/IntrusiveListExample3.fst) | Unary ready-flag payload and whole-item recovery after dequeue. |
| [`IntrusiveList`](helpers/IntrusiveList.fst) | Derived unit/nonindexed contracts and adapters. |

### Dependencies

Here **`A -> B` means A directly depends on B**. Names omit the `IntrusiveList`
prefix except for the unit module. Standard Pulse/F* libraries and generated
struct modules are omitted from this helper-only diagram.

```text
Ops      -> Indexed
Validate -> Indexed
Context  -> Indexed

Items    -> Indexed, Context
Insert   -> Indexed, Context
Remove   -> Indexed, Context

Example  -> Indexed, Context, Items
Example2 -> Indexed, Items
Example3 -> IntrusiveList

IntrusiveList (unit API) -> Indexed, Context
```

The generated C modules provide the remaining connections:

- `intrusive_list.c` uses Indexed, Context, Ops, and Validate annotations.
- The integer and resource clients combine their concrete Example helpers with
  the generic Items/Insert proofs; the integer client also uses Remove.
  Example helpers do not need to import those algorithm helpers merely because
  the C client uses both.
- The unit module calls the generated contracts for all nine `list_*` operations.
  Example also calls the generated `list_remove_head` contract in its
  list-valued-payload check.
- Generated `Struct_list_node` and `Struct_item*` modules supply the layout and
  field-ownership operations. Only concrete Example helpers depend on their
  corresponding item struct.

There is no dependency from the indexed foundation or primitive implementation
back to the unit API. Client3 brings the unit module into normal verification;
no separate sanity-check C file is needed.

## What the three clients prove

In the snippets below, `I` is the generated module for that client's item struct,
`R` is `Pulse.Lib.Reference`, and `X` is `IntrusiveListIndexed`.
`owner node` recovers the enclosing item from its embedded link. The generated
`__aux_raw_unfolded` predicate holds auxiliary struct ownership needed to
reconstruct the whole item. `**` combines separately owned resources;
`pure` states a fact without owning storage.

In every case, the list predicate owns the link storage separately from the
payload. Indexed descriptions are ghost values describing actual storage;
they do not replace ownership of that storage.

### `client.c`: indexed integer items

[`client.c`](client.c) embeds a link in an item with an integer value. The indexed
description records that value, while the payload owns the non-link item fields.

The concrete predicate in
[`IntrusiveListExample`](helpers/IntrusiveListExample.fst) is:

```fstar
let item_ipl : X.ipayload Int32.t =
  fun node value ->
    I.struct_item__aux_raw_unfolded (owner node) 1.0R **
    R.pts_to (I.struct_item__value_1 (owner node)) value
```

Thus an entry `(node, value)` owns the enclosing item's auxiliary resource and
its integer field containing exactly `value`. It does not own the link twice:
combining this payload with the separate link ownership recovers the whole item.

- `items_find` returns the first matching item, or `NULL`, without consuming
  the list or changing its descriptions.
- `items_pop_front` returns `NULL` for an empty list; otherwise it returns the
  first whole item and preserves the exact remaining sequence.
- `items_insert_sorted` requires a sorted list and preserves sortedness, placing
  a new item after existing items with equivalent values.
- `items_remove_value` preserves the order of survivors and returns detached
  ownership of all matching items; the resulting list has no match.

`list_example` combines insertion, lookup hit/miss, empty/nonempty moves,
filtering, pop, and sentinel/member validation, then recovers its stack storage.
Its helper also checks uninhabited descriptions for empty lists, nonempty
`emp` payloads, resource-owning list-valued descriptions, and stability for
equal-length list descriptions. These are proof instantiations, not extra
runtime list algorithms.

### `client2.c`: indexed arrays and external resources

[`client2.c`](client2.c) uses `struct item2` with a priority, a used count,
four inline unsigned samples, a pointer to an external processing counter,
and an embedded link.

The description records the metadata, samples, counter address, and counter
value. The payload owns the actual inline-array storage and the counter cell,
not just the pointer stored in the item. It also requires `used <= 4`.

[`IntrusiveListExample2`](helpers/IntrusiveListExample2.fst) defines the index
type and payload as follows (omitting proof-search attributes):

```fstar
noeq type description = {
  priority: Int32.t;
  used: UInt32.t;
  samples: full_array_lspec UInt32.t 4;
  counter: ref UInt32.t;
  count: UInt32.t;
}

let fields (item: item_ref) (d: description) : slprop =
  I.struct_item2__aux_raw_unfolded item 1.0R **
  R.pts_to (I.struct_item2__priority_1 item) d.priority **
  R.pts_to (I.struct_item2__used_1 item) d.used **
  array_pts_to (I.struct_item2__samples_1 item) 1.0R d.samples **
  R.pts_to (I.struct_item2__processed_1 item) d.counter **
  R.pts_to d.counter d.count ** pure (UInt32.v d.used <= 4)

let item_ipl (node: X.lref) (d: description) : slprop =
  fields (owner node) d
```

Here `item_ref` is a reference to `struct item2`, and `item_ipl` has the shape
`X.ipayload description`. The index captures more than the priority used for
sorting: it specifies all four samples, the valid prefix length, and the exact
external counter address and contents. In particular, owning the `processed`
pointer field and owning the cell it points to are two distinct resources.

- `items2_insert_sorted` preserves stable priority ordering and all attached
  resources, including the descriptions of existing entries.
- `items2_find` returns the first matching priority or `NULL`, preserving ownership.
- `items2_pop_front` returns whole detached-item ownership together with the
  external counter and preserves the exact tail.
- `item2_process_sample` requires detached ownership, `index < used`, and a
  counter below `4294967295`. It returns the specified sample and increments
  the counter by exactly one without wrapping. Samples, metadata, counter
  pointer, and link contents are preserved.

`list_example2` exercises equal priorities, lookup, empty/nonempty pop, sample
processing, and re-enqueueing with an updated description. All item, array,
counter, and sentinel resources are recovered. The helper's ownership
roundtrip checks that decomposing an item into links and payload and rejoining
them preserves those resources.

### `client3.c`: nonindexed ready-flag FIFO

[`client3.c`](client3.c) uses `struct item3` with a Boolean flag and an embedded
link. Its contracts track a sequence of node addresses, not indexed descriptions.
The unary payload requires every queued item's `ready` field to be `true`.

[`IntrusiveListExample3`](helpers/IntrusiveListExample3.fst) defines it using
`U = IntrusiveList`, the unit API:

```fstar
let ready_payload (node: U.lref) : slprop =
  I.struct_item3__aux_raw_unfolded (owner node) 1.0R **
  R.pts_to (I.struct_item3__ready_1 (owner node)) true

let payload : U.payload = U.of_unary ready_payload
```

`ready_payload` takes only a node, not a Boolean description. Its unit-indexed
adaptation satisfies `payload node () = ready_payload node`; the sole index
value is `()`, not `true`. The actual ready field is nevertheless owned and
fixed to `true` by the predicate itself.

- `items3_enqueue` sets `ready = true` and appends the item.
- `items3_dequeue` returns `NULL` when empty; otherwise it removes the first
  item, clears `ready`, and returns whole-item ownership with `ready == false`.
- `items3_append` appends the source sequence after the destination sequence
  and leaves the source empty.

Six verified static C adapters expose initialization, emptiness, sentinel
validation, tail insertion, nonempty head removal, and moving lists through
unindexed contracts. They call the same `list_*` primitives; unit-to-indexed
conversion stays inside their proof adapters rather than the queue algorithms.

`list_example3` proves FIFO pointer order, re-enqueueing, empty/nonempty appends,
flag transitions, and complete stack/sentinel ownership recovery. The uniform
true flag is a deliberate payload invariant, not a limitation of nonindexed
lists.

## Building and verifying

Use the repository's configured Clang/LLVM and F*/Pulse toolchain. From the
repository root:

```sh
# Build PAL and its Pulse support library, then verify and compile this test.
make
make -C test/intrusive_list -j8

# Run the complete test suite and formatting checks.
make test -j8
```

The test Makefile translates all its C files, verifies the generated Pulse
implementations/interfaces and reachable helpers, and compiles native object
files. It does **not** link or execute the example functions: native execution
requires a driver calling `list_example`, `list_example2`, and `list_example3`.

`out/`, `_cache/`, `obj/`, and `.depend` are generated artifacts. The `.fst`
files under `helpers/` are hand-maintained proofs. The Makefile, PAL header,
and configuration symlinks follow the shared test scaffold.

Assertions and assertion-only calls retain their enabled/disabled behavior.
When comparing native runs, exercise both ordinary and `NDEBUG` builds; ghost
annotations themselves do not add runtime reads or writes.

## Palow

This test verifies under both memory models from one set of C sources. The
Palow versions of the eleven helper modules live in `helpers_palow/`, under
the same module names as the originals; `test/palow-check.sh` prefers that
directory when it exists.

Two modules there have no counterpart in `helpers/`. `IntrusiveListNodeRef`
presents Palow's `struct_list_node` in the shape `Pulse.Lib.Reference` has, so
the generic list theory differs from its original only in a `module R = ...`
line. `IntrusiveListItemRefs` does the same for the three client structs.

Where the C used to name a model's own predicate -- `Pulse.Lib.Reference.pts_to`,
a field reference, an array's contents -- it now names a helper that each tree
defines for itself: `IntrusiveListIndexed.lpts_to`, `item_pts_to`, `item_link`,
`samples_of`. The `$unfold`/`$fold` pairs around field accesses stay in the C
because the current model needs them; Palow replaces them with the
`focus`/`unfocus` it writes itself.
