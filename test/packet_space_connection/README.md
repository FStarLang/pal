# PAL packet-space / connection ownership test

This isolated PAL regression test verifies a bidirectional `packet_space` /
`connection` ownership transfer. Its inputs are
[`packet_space_connection.c`](packet_space_connection.c) and
[`helpers/Helpers_PACKET_SPACE_CONNECTION.fst`](helpers/Helpers_PACKET_SPACE_CONNECTION.fst).

## Quantified capability

`PalPacketSpaceConnectionUpdate` receives PAL's automatic ownership for its
`_consumes packet_space*` parameter and exactly one additional capability. This
is the whiteboard capability, quantified over the **current** packet-space
value:

```text
packet_space_to_connection ps back back_ref =
  forall* ps_v.
    Trade.trade
      (R.pts_to ps ps_v ** pure (ps_v.connection == back_ref))
      (connection_owner ps ps_v (back ps_v))
```

`back` is a ghost function (`PS.struct_packet_space -> GTot C.struct_connection`)
mapping the current packet-space value to the connection value the owner still
holds; `GTot` is the faithful ghost form of the whiteboard's
`PS.struct_packet_space -> C.struct_connection`, so `back ps_v` is used directly
with no `reveal`/`erased` noise.

Quantifying over `ps_v` is exactly what keeps the packet space **mutable**. A
monomorphic trade pins one pre-mutation `ps_v` in its antecedent, so once the
scalar fields are written the pinned trade can no longer be fired — it forces the
packet space to be const. The `forall*` family instead carries one trade per
`ps_v`, and only the one whose antecedent `pts_to ps ps_v` the caller can supply
is ever fired, so the caller may mutate the scalar fields first.

### The one necessary deviation: `back_ref`

The whiteboard writes the capability with a single `back` parameter and the bare
antecedent `pts_to ps ps_v`. The extra `back_ref` parameter and the
`pure (ps_v.connection == back_ref)` conjunct are the single unavoidable
adaptation to the real `_core_ref` layout:

```text
connection_owner ps ps_v conn_v =
  R.pts_to ps ps_v
  ** R.pts_to (CoreRef.core_to_ref ps_v.connection) conn_v
  ** pure (conn_v.packet_space == ps)
```

`connection_owner` locates the connection through the reverse `_core_ref` field
`ps_v.connection`. Because the trade quantifies over **every** `ps_v`, without
pinning that field `create_packet_space_trade` is genuinely unprovable: for an
arbitrary `ps_v` it would have to produce
`pts_to (core_to_ref ps_v.connection) conn_v` from the single owned connection at
`core_to_ref back_ref` (F* rejects this with Error 228). The
`pure (ps_v.connection == back_ref)` premise supplies exactly the core_ref
equality each instance needs. The `connection` member is never written, so the C
precondition seeds it directly as `pure($(PacketSpace->connection) == back_ref)`
and it survives the two scalar writes.

The owner-side creator captures the immutable core reference as `back_ref` and
fixes the ghost `back` function to the owned connection value, then uses
`forall*` introduction to build every permitted trade instance from the same
connection root. No axiom, admit, unsafe escape, or monomorphic wrapper is used.

## Update ordering and result

The direct C update is intentionally ordered as follows:

1. write `largest_acknowledged` and `ack_needed`;
2. instantiate and eliminate the quantified trade using the current,
   post-mutation packet-space ownership and the `pure` core_ref equality;
3. reify the already-written packet scalar snapshot in PAL's returned owner
   root (the C values are unchanged);
4. follow `PacketSpace->connection`, then write `last_acknowledged` and
   `send_flags`.

Step 2 is the regression point: `forall*` does not commit the trade to the
pre-write `ps_v`, unlike the former monomorphic capability. The precise
postcondition states the two packet-space scalar values, the two connection
scalar values, and the reverse `connection.packet_space == PacketSpace` link.
`connection_owner` additionally owns the connection at
`CoreRef.core_to_ref(ps_v.connection)`, completing the other link direction.

## Validation

Run from this directory:

```sh
make clean && make verify
```

The local Makefile invokes only the repository-local PAL translator and F*
verification harness. See [`RESULT.md`](RESULT.md) for the recorded result and
additional focused checks.
