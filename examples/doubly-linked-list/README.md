# Doubly linked lists with separate proofs

This example verifies a caller-owned, circular intrusive doubly linked list and
an integer-item client. Public contracts stay in [`dll.h`](dll.h). The checked-in
[`dll.c`](dll.c) and [`client.c`](client.c) contain executable C, while their loop
invariants, ghost arguments, and proof steps live in
[`proofs.annotations`](proofs.annotations).

## Build

From a checkout with the [PAL toolchain](../../README.md#dependencies):

```sh
make -C examples/doubly-linked-list -j8
```

The default target builds PAL and its support library, then:

1. Copies the C files and header into `_build/annotated/`.
2. Checks and applies `proofs.annotations` using `pal_annotations`.
3. Translates both implementations and verifies every generated module and
   handwritten theory module with dependency-driven parallel F*/Pulse checks.
4. Compiles and runs native checks, both normally and with `NDEBUG`.
5. Checks overlay idempotence, byte-exact extract/apply roundtrips, and preservation
   of the header contracts and checked-in sources.

All generated files stay in `_build/`; `make clean` removes that directory.
Useful individual targets are `prepare`, `translate`, `verify`, `native`, and
`check-overlay`. `FSTAR_EXE`, `CC`, `CPPFLAGS`, `CFLAGS`, and `LDFLAGS` can be
overridden. `make native` needs only a C compiler, not PAL or F*.
The repository's `make test -j8` includes this example.

## API and ownership

An empty sentinel points to itself in both directions. Each member embeds a
`struct list_node`; the integer client's `link` is deliberately not its first
field. There is no allocation or deallocation.

| API | Contract |
|---|---|
| `list_init`, `list_empty` | Initialize an empty ring; test emptiness without changing it. |
| `list_validate` | Check both neighboring links of a sentinel or member. |
| `list_insert_head`, `list_insert_tail`, `list_insert_after` | Insert a detached node at the specified sequence position. |
| `list_remove`, `list_remove_head` | Remove a member and return its link/payload ownership. Removing the head requires a nonempty ring. |
| `list_move` | Append one disjoint ring to another and leave the source empty. |
| `items_find` | Traverse to the first matching value, or return `NULL`; preserve the exact list. |
| `items_insert_sorted` | Stable insertion into an already sorted list, preserving sortedness and the exact modeled sequence. |
| `items_remove_value` | Remove all matches while preserving the order of survivors; return ownership of the detached items. |
| `items_pop_front` | Return `NULL` for an empty list, or transfer ownership of the whole first item. |

`list_remove` reports whether the ring became empty; it does not clear the
removed node's old links. `items_find` returns a borrowed pointer, not a transfer
of ownership. `items_remove_value` does not free memory or return a pointer
array: callers retain the addresses of their objects, and its postcondition
returns ownership of exactly the matching objects.

`list_example` is a closed, verified stack-allocated client. It inserts and
traverses items, checks hits and misses, moves empty and nonempty lists, filters
an item, pops the remaining items, and recovers every sentinel and item before
returning. Its public contract is `emp` to `emp`: it needs no caller-owned
resources and retains none. The separate `native-check.c` harness additionally
tests forward/backward links, stable duplicate insertion, removal of multiple
matches, singleton removal, and reuse; it is a runtime test, not a proof target.

These are sequential memory-safety and functional-correctness guarantees under
the header's preconditions. They do not prove termination of every generated
Pulse function, concurrent safety, or behavior for arbitrary invalid pointers.
Executable C assertions remain in the sources. The client handles both
assertion-enabled and assertion-disabled paths; system headers precede `dll.h`
so PAL's assertion support is not overwritten by `<assert.h>`.

## Theory

The generic abstraction in `IntrusiveListIndexed.fst` is:

```fstar
ipayload a = lref -> a -> slprop
entries a = list (lref & a)
is_list_ring_ix payload head permission entries
```

Each entry owns its links and `payload node description`; the sentinel owns
links only. The sequence records node identity as well as payload descriptions,
so ordering and stable insertion are not merely properties of an unordered set.

| Modules in `theory/` | Role |
|---|---|
| `IntrusiveListNodeRef`, `IntrusiveListIndexed` | Link representation, indexed ring/segment predicates, sequence functions. |
| `IntrusiveListContext` | Erased packages for the C API's generic ghost arguments. |
| `IntrusiveListOps`, `IntrusiveListValidate` | Structural operations and neighboring-link borrowing. |
| `IntrusiveListItems`, `IntrusiveListInsert`, `IntrusiveListRemove` | Payload traversal, sorted insertion, and filtering lemmas. |
| `Dll.Item`, `Dll.Client` | Integer-item field ownership, concrete payload model, lookup and removal postconditions. |

The generic theory is shared with the existing
[`test/intrusive_list`](../../test/intrusive_list) clients through symlinks,
rather than maintained as two copies.

## Annotation workflow

Inspect `_build/annotated/` after `make prepare` to see the proof steps beside
the C statements they justify. The overlay contains TOML records with named
function owners and required local token context, not line-number patches.
Ambiguous or changed attachment sites are errors; applying an overlay does not
itself establish that its proofs remain valid.

For proof or implementation edits, work on the annotated copies:

```sh
cd examples/doubly-linked-list
make prepare
# Edit _build/annotated/dll.c and/or _build/annotated/client.c.
# Edit public contracts in dll.h, not in the temporary header copy.
../../target/debug/pal_annotations --root _build/annotated \
    --extract dll.c client.c -o _build/updated.annotations
cp _build/annotated/dll.c _build/annotated/client.c .
cp _build/updated.annotations proofs.annotations
make -j8
```

Choose a fresh output name if `_build/updated.annotations` already exists; the
tool refuses to overwrite an existing overlay. Do not pass `dll.h` to
`--extract`: that deliberately keeps the public specifications visible.
Only the selected `.c` files are stripped. The resulting overlay has paths
`dll.c` and `client.c`, so it can also be applied to another directory containing
those files using `--root`.

Standalone ghost statements and proof-only attribute lines disappear during
extraction. Empty C branches may remain where proofs distinguish the paths.
Some restored proof steps occur after a C `return`; PAL uses these to close the
proof before emitting its Pulse return. See
[the annotation format documentation](../../doc/annotations.md) for anchoring,
conflict handling, and exact-roundtrip guarantees.
