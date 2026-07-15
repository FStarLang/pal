# PAL packet-space / connection ownership test

This isolated PAL regression test verifies a bidirectional `packet_space` /
`connection` ownership transfer where the connection owns an **array** of
packet-space pointers (`packets[ENCRYPT_LEVEL_COUNT]`), mirroring MsQuic's
`QUIC_CONNECTION.Packets[QUIC_ENCRYPT_LEVEL_COUNT]`. Its inputs are
[`packet_space_connection.c`](packet_space_connection.c) and
[`helpers/Helpers_PACKET_SPACE_CONNECTION.fst`](helpers/Helpers_PACKET_SPACE_CONNECTION.fst).

## Layout

```c
typedef struct connection {
    packet_space* packets[ENCRYPT_LEVEL_COUNT];   /* = 3 */
    uint32_t last_acknowledged;
    uint32_t send_flags;
} connection;

struct packet_space {
    _core_ref connection* connection;   /* reverse core-ref back-pointer   */
    uint32_t encrypt_level;             /* which Packets[] slot it lives in */
    uint32_t largest_acknowledged;
    uint32_t ack_needed;
};
```

## Ownership predicate

The owner focuses **one** slot (`ps`) and keeps the other two slots plus the
connection allocation bundled:

```text
slot_owner br o = match o with
  | None   -> emp
  | Some p -> if is_null p then emp
              else exists* pv. pts_to p pv ** pure (pv.connection == br)

other_slots br pk k =           (* every slot except k *)
  (if k=0 then emp else slot_owner br pk[0])
  ** (if k=1 then emp else slot_owner br pk[1])
  ** (if k=2 then emp else slot_owner br pk[2])

connection_owner ps ps_v back_ref lvl pk conn_v =
  pts_to ps ps_v
  ** pts_to (core_to_ref ps_v.connection) conn_v
  ** other_slots back_ref pk (v lvl)
  ** pure (ps_v.connection == back_ref
        /\ ps_v.encrypt_level == lvl
        /\ conn_v.packets == pk
        /\ slot_at pk (v lvl) == Some ps
        /\ not (is_null ps))
```

`slot_at`/`other_slots` are parameterised by the immutable `packets` array field
(`pk : packets_t`), never by the whole `conn_v` — see the decoupling note below.

## Quantified capability

`PalPacketSpaceConnectionUpdate` receives PAL's automatic ownership for its
`_consumes packet_space*` parameter and exactly one additional capability — the
whiteboard capability, quantified over the **current** packet-space value:

```text
packet_space_to_connection ps back back_ref lvl pk =
  forall* ps_v.
    Trade.trade
      (pts_to ps ps_v ** pure (ps_v.connection == back_ref
                            /\ ps_v.encrypt_level == lvl))
      (connection_owner ps ps_v back_ref lvl pk (back ps_v))
```

`back : PS.struct_packet_space -> GTot C.struct_connection` maps the current
packet-space value to the connection value the owner still holds. Quantifying
over `ps_v` is what keeps the packet space **mutable**: a monomorphic trade pins
one pre-mutation `ps_v` in its antecedent, so once the scalar fields are written
the pinned trade can no longer be fired. The `forall*` family instead carries one
trade per `ps_v`; only the instance whose antecedent `pts_to ps ps_v` the caller
can supply is fired, so the caller may mutate the scalar fields first.

## Three immutable coordinates: `back_ref`, `lvl`, `pk`

The whiteboard writes the capability with a single `back` parameter and the bare
antecedent `pts_to ps ps_v`. The array layout forces three extra **stable
coordinates**, threaded as explicit parameters of `connection_owner`:

* `back_ref : core_ref` — the reverse `_core_ref` slot. Because the trade
  quantifies over every `ps_v`, without pinning this an arbitrary `ps_v` could
  redirect the core reference to an unowned connection.
* `lvl : uint32` — the encryption level, i.e. **which** array slot the packet
  space occupies. Without it a mutated `ps_v` could name a different slot and the
  forward link `slot_at pk (v lvl) == Some ps` would break.
* `pk : packets_t` — the `packets` array itself.

The `pure` clause ties each coordinate back to the concrete values
(`ps_v.connection == back_ref`, `ps_v.encrypt_level == lvl`,
`conn_v.packets == pk`).

### Why the coordinates must be *explicit* (the witness-selection fix)

The subtle failure this test pins down is Pulse **witness selection** when a
caller re-establishes `exists* ps_v … conn_v. connection_owner …` right after
writing scalar fields. If an existential (say `conn_v`) appears inside a slprop
atom only through a *projection* — e.g. `other_slots back_ref conn_v.packets …`
— then higher-order unification can bind that existential from the projection
argument to the **stale, pre-write** value (`?conn_v.packets =?= _conn_v34.packets`
⟹ `?conn_v := _conn_v34`) instead of from its unique `pts_to` pin. The pure
postcondition (`conn_v.last_acknowledged == PacketNumber`) is then checked against
the wrong value and fails (F* Error 19).

The fix is to make every existential appear **only** in its unique `pts_to` pin:

* `conn_v` appears only in `pts_to (core_to_ref ps_v.connection) conn_v`; the
  `packets` array is threaded as the separate coordinate `pk`.
* `ps_v` is pinned by `pts_to ps ps_v`; the slot index/back-ref are threaded as
  `lvl`/`back_ref`.

The single core_ref rewrite the layout still needs (from the fixed `back_ref`
address to the focused `ps_v.connection` address) is isolated inside
`restore_connection_owner`, where all values are explicit parameters.

## Update ordering and result

The direct C update is ordered as follows:

1. write `largest_acknowledged` and `ack_needed`;
2. instantiate and eliminate the quantified trade
   (`consume_packet_space_trade`) using the current, post-mutation packet-space
   ownership and the `pure` coordinate equalities;
3. reify the already-written packet scalar snapshot in PAL's returned owner root
   (the C values are unchanged);
4. follow `PacketSpace->connection`, then write `last_acknowledged` and
   `send_flags`.

The precise postcondition states the two packet-space scalar values and the two
connection scalar values, while `connection_owner` re-establishes ownership of
the connection and all array slots.

## Validation

Run from this directory:

```sh
make clean && make verify
```

The local Makefile invokes only the repository-local PAL translator and F*
verification harness. See [`RESULT.md`](RESULT.md) for the recorded result and
additional focused checks.
