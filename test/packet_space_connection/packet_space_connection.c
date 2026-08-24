#include "pal.h"
#include <stdint.h>

#define PACKET_SPACE_ACK_NOT_NEEDED 0u
#define CONNECTION_SEND_FLAGS_ACK_AND_FLUSH 3u

typedef struct packet_space packet_space;

#define ENCRYPT_LEVEL_COUNT 3

typedef struct connection {
    /* Models Connection->Packets[QUIC_ENCRYPT_LEVEL_COUNT]. */
    packet_space* packets[ENCRYPT_LEVEL_COUNT];
    uint32_t last_acknowledged;
    uint32_t send_flags;
} connection;

struct packet_space {
    _core_ref connection* connection;
    /* Which Packets[] slot (encryption level) this packet space lives in. */
    uint32_t encrypt_level;
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
        exists* back_ref back lvl pk.
            Helpers_PACKET_SPACE_CONNECTION.packet_space_to_connection
                $(PacketSpace) back back_ref lvl pk
            ** pure ($(PacketSpace->connection) == back_ref
                  /\ $(PacketSpace->encrypt_level) == lvl)))
    _ensures(_inline_pulse(
        exists* ps_v back_ref lvl pk conn_v.
            Helpers_PACKET_SPACE_CONNECTION.connection_owner
                $(PacketSpace) ps_v back_ref lvl pk conn_v
            ** pure (
                 ps_v.$field(struct packet_space::largest_acknowledged)
                     == $(PacketNumber)
              /\ UInt32.v ps_v.$field(struct packet_space::ack_needed) == 0
              /\ conn_v.$field(struct connection::last_acknowledged)
                     == $(PacketNumber)
              /\ UInt32.v conn_v.$field(struct connection::send_flags) == 3)))
{
    PacketSpace->largest_acknowledged = PacketNumber;
    PacketSpace->ack_needed = PACKET_SPACE_ACK_NOT_NEEDED;

    _ghost_stmt(
        Helpers_PACKET_SPACE_CONNECTION.consume_packet_space_trade $(PacketSpace));

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
        exists* ps_v back_ref lvl pk conn_v.
            Helpers_PACKET_SPACE_CONNECTION.connection_owner
                $(PacketSpace) ps_v back_ref lvl pk conn_v
            ** pure (
                 ps_v.$field(struct packet_space::largest_acknowledged)
                     == $(PacketNumber)
              /\ UInt32.v ps_v.$field(struct packet_space::ack_needed) == 0
              /\ conn_v.$field(struct connection::last_acknowledged)
                     == $(PacketNumber)
              /\ UInt32.v conn_v.$field(struct connection::send_flags) == 3)))
{
    _ghost_stmt(
        Helpers_PACKET_SPACE_CONNECTION.create_packet_space_trade $(PacketSpace));
    PalPacketSpaceConnectionUpdate(PacketSpace, PacketNumber);
}

/*
 * Models QuicPacketSpaceInitialize's create + install lifecycle in one step,
 * producing the full owner.
 *
 * `PacketSpace` arrives UNINITIALIZED (`pts_to_uninit`) because in real MsQuic
 * it is freshly allocated, so the packet-space invariant does not hold yet; a
 * `_consumes` parameter would demand the very invariant this function
 * establishes. Both pointers are therefore `_plain`, with the preconditions
 * written by hand, and `PacketSpace` is consumed into the resulting owner.
 *
 * The postcondition `connection_owner_exists` is exactly what the mutate
 * functions above consume, so the lifecycle chains:
 * Initialize => connection_owner_exists => borrow / mutate / restore.
 * See README.md for the full rationale.
 */
void
PalPacketSpaceInitialize(
    _plain connection* Connection,
    uint32_t EncryptLevel,
    _plain packet_space* PacketSpace
    )
    _requires(_inline_pulse(
        Helpers_PACKET_SPACE_CONNECTION.connection_slot_empty
            $(Connection) $(EncryptLevel)
        ** Pulse.Lib.Reference.pts_to_uninit $(PacketSpace)))
    _ensures(_inline_pulse(
        Helpers_PACKET_SPACE_CONNECTION.connection_owner_exists $(PacketSpace)))
{
    /* Turn raw memory into a valid packet space: open the per-field uninit reps,
     * populate every field, then fold to ESTABLISH the representation. */
    _ghost_stmt($unfold-uninit(packet_space) $(PacketSpace));
    PacketSpace->connection = Connection;
    PacketSpace->encrypt_level = EncryptLevel;
    PacketSpace->largest_acknowledged = 0;
    PacketSpace->ack_needed = PACKET_SPACE_ACK_NOT_NEEDED;
    _ghost_stmt($fold(packet_space) $(PacketSpace) _ _ _ _);

    /* Install into the connection's slot and deposit into the full owner. */
    Connection->packets[EncryptLevel] = PacketSpace;
    /* A live `pts_to PacketSpace _` proves the pointer is non-NULL, which the
     * deposit needs to record `slot_at ... == Some PacketSpace` with a live slot. */
    _ghost_stmt(Pulse.Lib.Reference.pts_to_not_null $(PacketSpace));
    _ghost_stmt(
        Helpers_PACKET_SPACE_CONNECTION.deposit
            $(PacketSpace) $(Connection) $(EncryptLevel));
}
