# Packet-space / connection verification result

Recorded 2026-07-14 from `test/packet_space_connection` in the PAL repository.

## Direct two-resource update contract

`PalPacketSpaceConnectionUpdate` declares `PacketSpace` as
`_consumes packet_space*`. PAL automatically emits the raw packet-space input
ownership, while the custom C-side requirement contains only the separate
`Pulse.Lib.Trade` resource plus the pure link from its witness to the received
value:

```text
exists* ps_v conn_v.
  Helpers_PACKET_SPACE_CONNECTION.packet_space_to_connection
    $(PacketSpace) ps_v conn_v **
  pure(ps_v == $(*PacketSpace))
```

The regenerated `out/Func_PalPacketSpaceConnectionUpdate.fsti` has this exact
automatic ownership requirement:

```text
requires
  exists* (val_packetspace_0: Typedef_packet_space.ty_packet_space).
  ((Pulse.Lib.Reference.pts_to var_packetspace #1.0R val_packetspace_0) **
    (Typedef_packet_space.ty_packet_space__pred (!var_packetspace) 1.0R))
```

It then has the separate existential trade requirement:

```text
requires
  (exists* ps_v conn_v.
    Helpers_PACKET_SPACE_CONNECTION.packet_space_to_connection
      var_packetspace ps_v conn_v **
    pure (ps_v == (!var_packetspace)))
```

There is **no** automatic packet-space ownership `ensures`. Its relevant
postcondition is the exact `connection_owner` root with all four scalar writes:

```text
ensures
  (exists* ps_v conn_v.
    Helpers_PACKET_SPACE_CONNECTION.connection_owner
      var_packetspace ps_v conn_v **
    pure (
      ps_v.largest_acknowledged == var_packetnumber /\
      UInt32.v ps_v.ack_needed == 0 /\
      conn_v.last_acknowledged == var_packetnumber /\
      UInt32.v conn_v.send_flags == 3))
```

`packet_space_to_connection` remains the one-use trade from raw packet-space
ownership to the complete `connection_owner` root. The consumer helper matches
that trade before the automatic raw ownership, then calls `Trade.elim_trade`;
no ownership is weakened or escaped. `packet_space.connection` is the
`_core_ref connection*` back-pointer and `connection.packet_space` is the
ordinary selected slot.

## Local verification

Exact command, run in `test/packet_space_connection`:

```sh
make clean && make verify
```

Result: **exit 0**. The standard local test Makefile invoked
`../../target/debug/pal` for translation and `../../opt/run-fstar.sh` for
verification. F* verified the generated typedef, struct, helper, interface,
function, and `TranslationErrors` modules; every reported module ended with
`All verification conditions discharged successfully`. F* also emitted two
non-fatal Warning 321 messages about prechecked `Pulse.Main` and `Pulse` module
locations during dependency generation.
