# Packet-space / connection verification result

Recorded 2026-07-14 from `test/packet_space_connection`.

## Whiteboard quantified trade

The capability is the whiteboard form:

```text
packet_space_to_connection ps back back_ref =
  forall* (ps_v: PS.struct_packet_space).
    T.trade
      (R.pts_to ps ps_v ** pure (ps_v.connection == back_ref))
      (connection_owner ps ps_v (back ps_v))
```

`back` is the ghost function `PS.struct_packet_space -> GTot C.struct_connection`
— the faithful ghost reading of the whiteboard's
`PS.struct_packet_space -> C.struct_connection` — so `back ps_v` is used
directly with no `reveal`. The only deviation from the whiteboard is the
`back_ref` parameter plus the inlined `pure (ps_v.connection == back_ref)`
conjunct, required by the real `_core_ref` layout.

This stability premise prevents an arbitrary universally quantified packet-space
value from redirecting the core reference to an unowned connection allocation.
It is not optional: because `connection_owner` locates the connection at
`CoreRef.core_to_ref ps_v.connection`, dropping the premise makes
`create_packet_space_trade` unprovable (F* Error 228 — it cannot produce
`pts_to (core_to_ref ps_v.connection) conn_v` for an arbitrary `ps_v` from the
single owned connection). The owner creates the capability from its complete
root by fixing `back_ref` to the original `ps_v.connection` and fixing `back` to
the owned connection witness. The proof uses `forall*` introduction and
elimination plus `Trade.trade`; it contains no axioms, admits, unsafe escapes,
or monomorphic wrapper.

## C update ordering and exact result

`PalPacketSpaceConnectionUpdate` has automatic `_consumes packet_space*`
ownership plus one separate `packet_space_to_connection` capability and the
pure C-level premise:

```text
pure($(PacketSpace->connection) == back_ref)
```

It writes the packet-space scalar fields first, then calls
`consume_packet_space_trade` to instantiate the `forall*` trade with the
post-mutation ownership, reifies the same scalar snapshot in the returned PAL
owner root, follows `PacketSpace->connection`, and writes the connection scalar
fields. Its postcondition gives:

- `PacketSpace->largest_acknowledged == PacketNumber`;
- `PacketSpace->ack_needed == 0`;
- `connection.last_acknowledged == PacketNumber`;
- `connection.send_flags == 3`;
- `connection.packet_space == PacketSpace`, while `connection_owner` owns that
  connection at `CoreRef.core_to_ref(ps_v.connection)`.

The critical distinction from the previous test is that `forall*` is spent at
the current packet-space value, so the first scalar writes do not force the
trade to be consumed early.

## Validation

```sh
make clean && make verify
```

Result: **exit 0**. PAL translation and all generated helper, interface,
function, and translation-error modules verified successfully. F* emitted only
the environment's two non-fatal Warning 321 notices about prechecked `Pulse`
module locations during dependency generation.

The final focused checks also use a no-escape grep and warning-clean native
compilation of `packet_space_connection.c`; both are recorded as passing after
the verification command.
