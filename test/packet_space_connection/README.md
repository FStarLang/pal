# PAL packet-space / connection ownership test

This self-contained PAL regression test verifies the direct two-resource
interface of `PalPacketSpaceConnectionUpdate`. Its inputs are
[`packet_space_connection.c`](packet_space_connection.c) and
[`helpers/Helpers_PACKET_SPACE_CONNECTION.fst`](helpers/Helpers_PACKET_SPACE_CONNECTION.fst).
It follows the standard local PAL test layout: the local `pal.h` and Makefile
are links to the test-suite support files, and helper proofs live in `helpers/`.
No MS-Quic repository files are required.

## Direct update interface

`PacketSpace` is a `_consumes packet_space*` parameter. PAL therefore generates
its raw full-ownership requirement; the C-side custom `_requires` carries only
the separate trade and a pure witness link (not another raw ownership resource):

```text
exists* ps_v conn_v.
  Helpers_PACKET_SPACE_CONNECTION.packet_space_to_connection
    $(PacketSpace) ps_v conn_v **
  pure(ps_v == $(*PacketSpace))
```

The generated interface has the corresponding automatic input requirement:

```text
exists* val_packetspace_0.
  Pulse.Lib.Reference.pts_to var_packetspace #1.0R val_packetspace_0 **
  Typedef_packet_space.ty_packet_space__pred (!var_packetspace) 1.0R
```

There is no automatic `PacketSpace` ownership `ensures`: `_consumes` transfers
that raw allocation into the concrete postcondition below. The direct API is
thus automatic consumed packet-space ownership plus one separate
`Pulse.Lib.Trade` capability.

`packet_space_to_connection` uses the installed `Pulse.Lib.Trade.trade` API:

```text
packet_space_to_connection ps ps_v conn_v =
  Trade.trade (R.pts_to ps ps_v) (connection_owner ps ps_v conn_v)
```

The trade conclusion is the complete `connection_owner` root:

```text
R.pts_to ps ps_v **
R.pts_to (CoreRef.core_to_ref(connection, ps_v.connection)) conn_v **
pure(conn_v.packet_space == ps)
```

It includes the packet-space allocation as well as the converted connection
allocation and reverse link, so spending the trade cannot lose packet-space
ownership. `packet_space.connection` has the actual `_core_ref connection*`
layout; `connection.packet_space` is the ordinary selected `packet_space*` slot,
so only the first direction uses `CoreRef.core_to_ref`.

After spending the trade, the C postcondition is concrete and keeps the exact
`connection_owner` root:

```text
exists* ps_v conn_v.
  connection_owner(PacketSpace, ps_v, conn_v) **
  pure(ps_v.largest_acknowledged == PacketNumber /\
       UInt32.v ps_v.ack_needed == 0 /\
       conn_v.last_acknowledged == PacketNumber /\
       UInt32.v conn_v.send_flags == 3)
```

The small consumer helper matches the trade before PAL's automatic consumed
ownership, introduces the shared witnesses, and calls `Trade.elim_trade`; the
owner-only helper creates the separate trade before calling the update.

## Validation

Run from this directory using PAL-repository-local tooling:

```sh
make clean && make verify
```

This invokes `../../target/debug/pal` and `../../opt/run-fstar.sh` through the
standard test Makefile. See [`RESULT.md`](RESULT.md) for the recorded command
and result. Generated PAL modules, F* cache files, and C objects remain local
under `out/`, `_cache/`, and `obj/`.
