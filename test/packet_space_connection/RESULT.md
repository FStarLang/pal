# Packet-space / connection verification result

Recorded from `test/packet_space_connection`.

The connection owns an **array** of packet-space pointers
(`packets[ENCRYPT_LEVEL_COUNT]`, N = 3), matching MsQuic's
`QUIC_CONNECTION.Packets[QUIC_ENCRYPT_LEVEL_COUNT]`. The owner focuses one slot
and bundles the remaining slots (NULL slot ⇒ `emp`) plus the connection
allocation.

## Whiteboard quantified trade

The capability is the whiteboard form, extended with three stable coordinates:

```text
packet_space_to_connection ps back back_ref lvl pk =
  forall* (ps_v: PS.struct_packet_space).
    T.trade
      (R.pts_to ps ps_v ** pure (ps_v.connection == back_ref
                              /\ ps_v.encrypt_level == lvl))
      (connection_owner ps ps_v back_ref lvl pk (back ps_v))
```

`back : PS.struct_packet_space -> GTot C.struct_connection` maps the current
packet-space value to the connection value the owner still holds, so `back ps_v`
is used directly with no `reveal`. Quantifying over `ps_v` keeps the packet space
mutable: only the instance whose antecedent `pts_to ps ps_v` the caller can
supply is fired, so scalar fields may be written first.

## Three immutable coordinates and the witness-selection fix

The array layout forces three stable coordinates, threaded as **explicit**
parameters of `connection_owner ps ps_v back_ref lvl pk conn_v`:

- `back_ref : core_ref` — the reverse `_core_ref` slot (prevents an arbitrary
  `ps_v` redirecting the core reference to an unowned connection);
- `lvl : uint32` — the encryption level / array slot index;
- `pk : packets_t` — the immutable `packets` array field.

Threading them explicitly is not cosmetic. If an existential appears in a slprop
atom only via a *projection* (e.g. `other_slots back_ref conn_v.packets …`),
Pulse's higher-order unifier can bind that existential to the **stale pre-write**
value from the projection argument rather than from its unique `pts_to` pin, and
the pure postcondition is then checked against the wrong value (F* Error 19).
Making each existential (`ps_v`, `conn_v`) appear only in its unique `pts_to`
pin, with `back_ref`/`lvl`/`pk` carried separately, removes the ambiguity. The
one core_ref address rewrite the layout still needs is isolated in
`restore_connection_owner`, where every value is an explicit parameter. The proof
uses `forall*` introduction/elimination plus `Trade.trade`; it contains no
axioms, admits, unsafe escapes, or monomorphic wrapper.

## C update ordering and exact result

`PalPacketSpaceConnectionUpdate` has automatic `_consumes packet_space*`
ownership plus one separate `packet_space_to_connection` capability and the pure
C-level premise:

```text
pure($(PacketSpace->connection) == back_ref /\ $(PacketSpace->encrypt_level) == lvl)
```

It writes the packet-space scalar fields first, calls
`consume_packet_space_trade` to instantiate the `forall*` trade with the
post-mutation ownership, reifies the same scalar snapshot in the returned owner
root, follows `PacketSpace->connection`, and writes the connection scalar fields.
Its postcondition gives:

- `PacketSpace->largest_acknowledged == PacketNumber`;
- `PacketSpace->ack_needed == 0`;
- `connection.last_acknowledged == PacketNumber`;
- `connection.send_flags == 3`;

with `connection_owner` re-establishing ownership of the connection (at
`CoreRef.core_to_ref(ps_v.connection)`) and all array slots.

## Validation

```sh
make clean && make verify
```

Result: **exit 0**. PAL translation and all generated helper, interface,
function, and translation-error modules verified successfully. Native
compilation of `packet_space_connection.c` (`make compile`) also succeeds.
