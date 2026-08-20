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
                 ps_v.Struct_packet_space.struct_packet_space__largest_acknowledged
                     == $(PacketNumber)
              /\ UInt32.v ps_v.Struct_packet_space.struct_packet_space__ack_needed == 0
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
        exists* ps_v back_ref lvl pk conn_v.
            Helpers_PACKET_SPACE_CONNECTION.connection_owner
                $(PacketSpace) ps_v back_ref lvl pk conn_v
            ** pure (
                 ps_v.Struct_packet_space.struct_packet_space__largest_acknowledged
                     == $(PacketNumber)
              /\ UInt32.v ps_v.Struct_packet_space.struct_packet_space__ack_needed == 0
              /\ conn_v.Struct_connection.struct_connection__last_acknowledged
                     == $(PacketNumber)
              /\ UInt32.v conn_v.Struct_connection.struct_connection__send_flags == 3)))
{
    _ghost_stmt(
        Helpers_PACKET_SPACE_CONNECTION.create_packet_space_trade $(PacketSpace));
    PalPacketSpaceConnectionUpdate(PacketSpace, PacketNumber);
}

/*
 * Models QuicPacketSpaceInitialize's create + install lifecycle FAITHFULLY, in
 * one step, producing the full owner.
 *
 * Faithfulness point (why `PacketSpace` comes in UNINITIALIZED): in real MsQuic
 * the packet space is FRESHLY ALLOCATED (`CxPlatPoolAlloc`), so its memory is
 * uninitialized when initialization begins -- the packet-space invariant does
 * NOT hold yet, and it would be nonsensical to require it. A `_consumes
 * packet_space*` would instead demand a fully-formed packet space (`__pred`
 * already holding) BEFORE the call, i.e. require the very invariant that
 * initialization is supposed to establish. So the storage comes in as
 * `pts_to_uninit` (raw memory, exactly the `_pal_pool_alloc_*` wrapper shape),
 * and the body ESTABLISHES the representation by writing every field, installs
 * it into the connection's NULL slot, and deposits into the full owner.
 *
 * Postcondition: `connection_owner_exists` -- the connection now owns the
 * connection allocation, every previously-owned slot, AND the freshly created
 * packet space in slot `EncryptLevel` (None/NULL -> Some ps). This is the exact
 * shape the mutate-existing owner functions consume, so the full lifecycle
 * chains: Initialize => connection_owner_exists => (borrow / mutate / restore).
 *
 * `PacketSpace` is `_plain` so PAL emits no automatic `_out`/`_consumes`
 * ownership: the uninitialized precondition is stated by hand, and the
 * packet-space pointer is CONSUMED into the owner (no residual standalone
 * ownership to return).
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
