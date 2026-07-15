/*
 * Isolated packet_space <-> connection bidirectional-link ownership test.
 * This file is translated for proof but is not part of a production build.
 *
 * The selected packet-space pointer is only an address and the packet-space
 * connection back-pointer is a proof-only core reference; neither grants
 * ownership of the separately allocated peer. A root owner creates one
 * quantified Pulse.Lib.Trade capability while it owns both allocations. The
 * trade is instantiated with the packet-space value after its scalar fields
 * have changed, provided its immutable core-reference back-pointer is stable.
 */

#include "pal.h"
#include <stdint.h>

#define PACKET_SPACE_ACK_NOT_NEEDED 0u
#define CONNECTION_SEND_FLAGS_ACK_AND_FLUSH 3u

typedef struct packet_space packet_space;

typedef struct connection {
    /* Models one selected Connection->Packets[] pointer slot. */
    packet_space* packet_space;
    uint32_t last_acknowledged;
    uint32_t send_flags;
} connection;

struct packet_space {
    _core_ref connection* connection;
    uint32_t largest_acknowledged;
    uint32_t ack_needed;
};

/*
 * Receives PAL-generated raw packet-space ownership and one separate
 * quantified capability. The explicit pure equality preserves the _core_ref
 * reverse slot captured by the capability while scalar fields are changed.
 */
void
PalPacketSpaceConnectionUpdate(
    _consumes packet_space* PacketSpace,
    uint32_t PacketNumber
    )
    _requires(_inline_pulse(
        exists* back_ref back.
            Helpers_PACKET_SPACE_CONNECTION.packet_space_to_connection
                $(PacketSpace) back back_ref
            ** pure ($(PacketSpace->connection) == back_ref)))
    _ensures(_inline_pulse(
        exists* ps_v conn_v.
            Helpers_PACKET_SPACE_CONNECTION.connection_owner
                $(PacketSpace) ps_v conn_v
            ** pure (
                 $(PacketSpace->largest_acknowledged) == $(PacketNumber)
              /\ UInt32.v $(PacketSpace->ack_needed) == 0
              /\ conn_v.Struct_connection.struct_connection__packet_space
                     == $(PacketSpace)
              /\ conn_v.Struct_connection.struct_connection__last_acknowledged
                     == $(PacketNumber)
              /\ UInt32.v conn_v.Struct_connection.struct_connection__send_flags == 3)))
{
    PacketSpace->largest_acknowledged = PacketNumber;
    PacketSpace->ack_needed = PACKET_SPACE_ACK_NOT_NEEDED;

    _ghost_stmt(
        Helpers_PACKET_SPACE_CONNECTION.consume_packet_space_trade $(PacketSpace));

    /* Reify the already-written scalar snapshot in the returned owner root. */
    PacketSpace->largest_acknowledged = PacketNumber;
    PacketSpace->ack_needed = PACKET_SPACE_ACK_NOT_NEEDED;
    connection* Connection = PacketSpace->connection;

    Connection->last_acknowledged = PacketNumber;
    Connection->send_flags = CONNECTION_SEND_FLAGS_ACK_AND_FLUSH;
}

/*
 * Demonstrates the owner-side protocol: create the quantified trade from a
 * root containing both allocations, call the focused update, and return its
 * precise concrete postcondition.
 */
void
PalPacketSpaceConnectionOwnerUpdate(
    _plain packet_space* PacketSpace,
    uint32_t PacketNumber
    )
    _requires(_inline_pulse(
        Helpers_PACKET_SPACE_CONNECTION.connection_owner_exists $(PacketSpace)))
    _ensures(_inline_pulse(
        exists* ps_v conn_v.
            Helpers_PACKET_SPACE_CONNECTION.connection_owner
                $(PacketSpace) ps_v conn_v
            ** pure (
                 $(PacketSpace->largest_acknowledged) == $(PacketNumber)
              /\ UInt32.v $(PacketSpace->ack_needed) == 0
              /\ conn_v.Struct_connection.struct_connection__packet_space
                     == $(PacketSpace)
              /\ conn_v.Struct_connection.struct_connection__last_acknowledged
                     == $(PacketNumber)
              /\ UInt32.v conn_v.Struct_connection.struct_connection__send_flags == 3)))
{
    _ghost_stmt(
        Helpers_PACKET_SPACE_CONNECTION.create_packet_space_trade $(PacketSpace));
    PalPacketSpaceConnectionUpdate(PacketSpace, PacketNumber);
}
