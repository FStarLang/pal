module Helpers_PACKET_SPACE_CONNECTION

open Pulse
open Pulse.Lib.C
#lang-pulse

module C = Struct_connection
module PS = Struct_packet_space
module R = Pulse.Lib.Reference
module T = Pulse.Lib.Trade
module CR = Pulse.Lib.C.CoreRef
module CA = Pulse.Lib.C.Array
module U32 = FStar.UInt32

// The connection now owns an ARRAY of packet-space pointers
// (`connection.packets[ENCRYPT_LEVEL_COUNT]`, mirroring MsQuic
// `QUIC_CONNECTION.Packets[QUIC_ENCRYPT_LEVEL_COUNT]`). A full connection owner
// therefore retains the connection allocation AND every non-NULL slot's packet
// space. One slot is "focused" (split out as raw ownership handed to a callee);
// the others stay bundled in `other_slots`.

// The `packets` array's pure representation and a total slot accessor.
// Parameterizing `other_slots`/`slot_at` on the array field alone (not the whole
// connection value) keeps these slprops stable across writes to the connection's
// *scalar* fields: `{conn_v with last_acknowledged = _}.packets` reduces (iota)
// back to `conn_v.packets`, so the framed atom still matches.
let packets_t = CA.full_array_lspec (ref PS.struct_packet_space) 3

// Field accessors. `unfold` makes them transparent to the SMT solver and to
// Pulse's slprop matcher, so they are purely cosmetic — every proof below sees
// exactly the projection it would have seen written out longhand.
unfold let conn_of (v: PS.struct_packet_space) = v.PS.struct_packet_space__connection
unfold let lvl_of (v: PS.struct_packet_space) = v.PS.struct_packet_space__encrypt_level
unfold let packets_of (v: C.struct_connection) = v.C.struct_connection__packets

let slot_at (pk: packets_t) (i: nat)
  : GTot (option (ref PS.struct_packet_space)) =
  CA.array_spec_get pk i

// Writing slot `i` leaves every other slot alone. Exposed as an SMT rewrite so
// that folding `other_slots` after a slot write matches the unfocused slots
// automatically, instead of needing an explicit `rewrite` per slot.
let slot_at_set_ne (pk: packets_t) (i j: nat) (x: ref PS.struct_packet_space)
  : Lemma (requires j <> i /\ i < 3 /\ j < 3)
          (ensures slot_at (CA.array_spec_set pk i (Some x)) j == slot_at pk j)
          [SMTPat (slot_at (CA.array_spec_set pk i (Some x)) j)] = ()

// Ownership of the packet space a slot pointer refers to. A NULL (or absent)
// slot owns nothing; a live slot owns its whole packet space and pins the
// proof-only core-reference back-pointer to the owning connection `br`.
let slot_owner (br: CR.core_ref)
               (o: option (ref PS.struct_packet_space)) : slprop =
  match o with
  | None -> emp
  | Some p ->
    if R.is_null p then emp
    else exists* (pv: PS.struct_packet_space).
           R.pts_to p pv
           ** pure ((conn_of pv) == br)

// Ownership of every slot EXCEPT the focused index `k`, whose contribution is
// `emp` because its packet space travels separately as `pts_to ps`. With only
// three encryption levels this is a fixed three-way bundle.
let slot_owner_at (br: CR.core_ref) (pk: packets_t) (k j: nat) : slprop =
  if k = j then emp else slot_owner br (slot_at pk j)

let other_slots (br: CR.core_ref) (pk: packets_t) (k: nat) : slprop =
  slot_owner_at br pk k 0 ** slot_owner_at br pk k 1 ** slot_owner_at br pk k 2

// A connection owner focused on packet space `ps` (which lives in slot `lvl`).
// It retains: the focused packet space, the connection allocation (reached
// through the core reference `back_ref`), and every other slot.
//
// KEY DESIGN POINT (witness selection): the two *stable* coordinates of the
// focus — `back_ref` and `lvl` — are EXPLICIT parameters, NOT projections of
// `ps_v`, so that `ps_v` appears only in `pts_to ps ps_v` and Pulse's unifier
// cannot bind it to a stale pre-write value. See README.md, "Why the
// coordinates must be *explicit*".
[@@pulse_unfold]
let connection_owner
  (ps: ref PS.struct_packet_space)
  (ps_v: PS.struct_packet_space)
  (back_ref: CR.core_ref)
  (lvl: U32.t)
  (pk: packets_t)
  (conn_v: C.struct_connection)
  : slprop =
  R.pts_to ps ps_v
  ** R.pts_to (CR.core_to_ref C.struct_connection
                (conn_of ps_v)) conn_v
  ** other_slots back_ref pk (U32.v lvl)
  ** pure ((conn_of ps_v) == back_ref
           /\ (lvl_of ps_v) == lvl
           /\ (packets_of conn_v) == pk
           /\ slot_at pk (U32.v lvl) == Some ps
           /\ not (R.is_null ps))

// A complete owner, with the stable coordinates fixed to the focused packet
// space's own back-pointer / level. This is the natural INPUT shape for an owner
// that still holds a concrete `ps_v` (nothing has been mutated yet).
[@@pulse_unfold]
let connection_owner_exists (ps: ref PS.struct_packet_space) : slprop =
  exists* (ps_v: PS.struct_packet_space) (conn_v: C.struct_connection).
    connection_owner ps ps_v
      (conn_of ps_v)
      (lvl_of ps_v)
      (packets_of conn_v)
      conn_v

// The whiteboard capability, generalized to the array layout:
//
//   forall* ps_v. trade (pts_to ps ps_v) (connection_owner ps ps_v (back ps_v))
//
// `back` maps the *current* packet-space value to the connection value the
// owner still holds. Quantifying over `ps_v` is what keeps the packet space
// mutable. The antecedent pins the two immutable coordinates `back_ref` (the
// _core_ref reverse slot) and `lvl` (which array slot `ps` occupies), so that an
// arbitrary quantified `ps_v` cannot redirect the core reference or name a
// different slot. See README.md, "Three immutable coordinates".
let packet_space_to_connection
  (ps: ref PS.struct_packet_space)
  (back: PS.struct_packet_space -> GTot C.struct_connection)
  (back_ref: CR.core_ref)
  (lvl: U32.t)
  (pk: packets_t)
  : slprop =
  forall* (ps_v: PS.struct_packet_space).
    T.trade
      (R.pts_to ps ps_v
       ** pure ((conn_of ps_v) == back_ref
                /\ (lvl_of ps_v) == lvl))
      (connection_owner ps ps_v back_ref lvl pk (back ps_v))

// Recombine the fixed connection allocation and the residual slots with a
// current focused packet-space value. The one rewrite re-keys the connection
// allocation from `back_ref` onto `conn_of ps_v` (equal by the `pure` clause,
// but Pulse's matcher does not consult SMT for slprop arguments).
// `connection_owner` must name the connection by the packet space's OWN
// projection so that C-level `PacketSpace->connection` dereferences match it.
ghost fn restore_connection_owner
  (ps: ref PS.struct_packet_space)
  (ps_v: PS.struct_packet_space)
  (back_ref: CR.core_ref)
  (lvl: U32.t)
  (pk: packets_t)
  (conn_v: C.struct_connection)
  requires R.pts_to ps ps_v
  requires pure ((conn_of ps_v) == back_ref
                 /\ (lvl_of ps_v) == lvl
                 /\ (packets_of conn_v) == pk)
  requires R.pts_to (CR.core_to_ref C.struct_connection back_ref) conn_v
  requires other_slots back_ref pk (U32.v lvl)
  requires pure (slot_at pk (U32.v lvl) == Some ps
                 /\ not (R.is_null ps))
  ensures connection_owner ps ps_v back_ref lvl pk conn_v
{
  rewrite (R.pts_to (CR.core_to_ref C.struct_connection back_ref) conn_v)
       as (R.pts_to (CR.core_to_ref C.struct_connection
                       (conn_of ps_v)) conn_v);
  fold (connection_owner ps ps_v back_ref lvl pk conn_v)
}

// An owner mints the capability from its complete root. It captures the
// immutable core_ref as `back_ref`, the encryption level as `lvl`, and fixes
// `back` to the owned connection value. The forall* introduction rebuilds every
// trade instance from the single residual (connection allocation + other slots)
// plus that instance's focused packet-space ownership.
ghost fn create_packet_space_trade (ps: ref PS.struct_packet_space)
  requires connection_owner_exists ps
  ensures exists* (ps_v: PS.struct_packet_space) (back_ref: CR.core_ref)
    (lvl: U32.t) (pk: packets_t)
    (back: PS.struct_packet_space -> GTot C.struct_connection).
    R.pts_to ps ps_v
    ** packet_space_to_connection ps back back_ref lvl pk
    ** pure ((conn_of ps_v) == back_ref
             /\ (lvl_of ps_v) == lvl)
{
  unfold (connection_owner_exists ps);
  with ps_v conn_v. assert (
    connection_owner ps (reveal ps_v)
      (conn_of (reveal ps_v))
      (lvl_of (reveal ps_v))
      (packets_of (reveal conn_v))
      (reveal conn_v));
  unfold (connection_owner ps (reveal ps_v)
      (conn_of (reveal ps_v))
      (lvl_of (reveal ps_v))
      (packets_of (reveal conn_v))
      (reveal conn_v));
  intro (forall* (ps_v_out: PS.struct_packet_space).
    T.trade
      (R.pts_to ps ps_v_out
       ** pure ((conn_of ps_v_out)
                  == (conn_of (reveal ps_v))
                /\ (lvl_of ps_v_out)
                  == (lvl_of (reveal ps_v))))
      (connection_owner ps ps_v_out
        (conn_of (reveal ps_v))
        (lvl_of (reveal ps_v))
        (packets_of (reveal conn_v))
        ((fun _ -> reveal conn_v) ps_v_out)))
    #(
      R.pts_to
        (CR.core_to_ref C.struct_connection
           (conn_of (reveal ps_v)))
        (reveal conn_v)
      ** other_slots (conn_of (reveal ps_v))
           (packets_of (reveal conn_v))
           (U32.v (lvl_of (reveal ps_v)))
      ** pure (
           slot_at (packets_of (reveal conn_v))
             (U32.v (lvl_of (reveal ps_v)))
             == Some ps
           /\ not (R.is_null ps)))
    fn _ ps_v_out {
      restore_connection_owner
        ps
        ps_v_out
        ((conn_of (reveal ps_v)))
        ((lvl_of (reveal ps_v)))
        ((packets_of (reveal conn_v)))
        (reveal conn_v)
    };
  fold (packet_space_to_connection ps
    (fun _ -> reveal conn_v)
    (conn_of (reveal ps_v))
    (lvl_of (reveal ps_v))
    (packets_of (reveal conn_v)));
}

// Spend the quantified capability: after the callee has mutated the focused
// packet space (keeping its core_ref and level stable) recover full ownership.
//
// `ps_v` is an IMPLICIT PARAMETER, not an existential of the ensures, so the
// caller keeps knowing exactly which packet-space value it gets back — in
// particular any scalar fields it wrote just before calling. (When `ps_v` was
// re-quantified in the ensures the caller lost that link and had to re-write
// the fields to recover it, emitting redundant C stores.) `back_ref`/`lvl` stay
// separate existentials so the returned owner stays decoupled — see
// `connection_owner`.
ghost fn consume_packet_space_trade
  (#ps_v: PS.struct_packet_space)
  (ps: ref PS.struct_packet_space)
  requires exists* (back_ref: CR.core_ref)
    (lvl: U32.t) (pk: packets_t)
    (back: PS.struct_packet_space -> GTot C.struct_connection).
    packet_space_to_connection ps back back_ref lvl pk
    ** R.pts_to ps ps_v
    ** pure ((conn_of ps_v) == back_ref
             /\ (lvl_of ps_v) == lvl)
  ensures exists* (back_ref: CR.core_ref)
    (lvl: U32.t) (pk: packets_t) (conn_v: C.struct_connection).
    connection_owner ps ps_v back_ref lvl pk conn_v
{
  with back_ref lvl pk back. assert (
    packet_space_to_connection ps (reveal back) (reveal back_ref) (reveal lvl)
      (reveal pk)
    ** R.pts_to ps ps_v
    ** pure ((conn_of ps_v) == (reveal back_ref)
             /\ (lvl_of ps_v) == (reveal lvl)));
  unfold (packet_space_to_connection ps (reveal back) (reveal back_ref) (reveal lvl)
    (reveal pk));
  Pulse.Lib.Forall.elim_forall ps_v;
  T.elim_trade
    (R.pts_to ps ps_v
     ** pure ((conn_of ps_v) == (reveal back_ref)
              /\ (lvl_of ps_v) == (reveal lvl)))
    (connection_owner ps ps_v (reveal back_ref) (reveal lvl) (reveal pk)
       ((reveal back) ps_v));
}
// ============================================================================
//  Create + install lifecycle (models QuicPacketSpaceInitialize).
//
//  The theory above is borrow/return of an ALREADY-owned focused packet space.
//  Initialization is a different lifecycle: it turns a connection whose target
//  slot is NULL (owning nothing there) into a full owner of a FRESHLY created
//  packet space in that slot (None/NULL -> Some ps). The two helpers below are
//  the entry predicate and the deposit that folds the new packet space into
//  `connection_owner`.
// ============================================================================

// The pre-state of initialization. The connection is owned BY VALUE (so its
// `packets[]` array field is writable through PAL's auto fold/unfold), the
// target slot `lvl` is NULL (owns nothing), and every other slot is already
// owned. The reverse core reference is the connection's own `ref_to_core conn`,
// matching the value the fresh packet space will store in its back-pointer.
[@@pulse_unfold]
let connection_slot_empty (conn: ref C.struct_connection) (lvl: U32.t) : slprop =
  exists* (conn_v: C.struct_connection) (pk: packets_t).
    R.pts_to conn conn_v
    ** other_slots (CR.ref_to_core conn) pk (U32.v lvl)
    ** pure ((packets_of conn_v) == pk
             /\ U32.v lvl < 3
             /\ slot_at pk (U32.v lvl) == Some (R.null #PS.struct_packet_space))

// Writing slot `k` leaves slot `j`'s ownership untouched: for j =/= k the two
// sides are the same `slot_owner` because `array_spec_set` agrees with the
// original spec off `k` (`slot_at_set_ne`); for j == k both sides are `emp`.
ghost fn slot_owner_at_set_stable
  (br: CR.core_ref) (pk: packets_t) (k j: nat) (newptr: ref PS.struct_packet_space)
  requires slot_owner_at br pk k j ** pure (k < 3 /\ j < 3)
  ensures slot_owner_at br (CA.array_spec_set pk k (Some newptr)) k j
{
  rewrite (slot_owner_at br pk k j)
       as (slot_owner_at br (CA.array_spec_set pk k (Some newptr)) k j)
}

// Writing slot `i` leaves every OTHER slot's ownership untouched.
ghost fn other_slots_set_stable
  (br: CR.core_ref) (pk: packets_t) (i: nat) (newptr: ref PS.struct_packet_space)
  requires other_slots br pk i ** pure (i < 3)
  ensures other_slots br (CA.array_spec_set pk i (Some newptr)) i
{
  unfold (other_slots br pk i);
  slot_owner_at_set_stable br pk i 0 newptr;
  slot_owner_at_set_stable br pk i 1 newptr;
  slot_owner_at_set_stable br pk i 2 newptr;
  fold (other_slots br (CA.array_spec_set pk i (Some newptr)) i)
}

// PAL's `array_write` emits `array_spec_upd s i v` (a RAW value write); the
// ownership theory speaks in `array_spec_set s i (Some v)` (an OPTIONAL value, so
// that NULL/absent slots read back as `None`). The two agree pointwise -- same
// length, mask, initialized-ness and value at every index, on and off `i` -- so
// they are extensionally equal (all four `array_spec_ext` hypotheses discharge
// from the matching `_upd_*`/`_set_*` SMT-pattern lemmas). Exposed as an SMT
// rewrite so the deposit call at the initializer site (whose context carries
// `conn_v.packets == array_spec_upd old_pk (v lvl) ps`) matches deposit's
// `array_spec_set old_pk (v lvl) (Some ps)` precondition.
let array_spec_upd_set_eq (#a: Type) (s: CA.array_spec a) (n: nat) (x: a)
  : Lemma (CA.array_spec_upd s n x == CA.array_spec_set s n (Some x))
          [SMTPat (CA.array_spec_upd s n x)]
  = CA.array_spec_ext (CA.array_spec_upd s n x) (CA.array_spec_set s n (Some x))

// Deposit the freshly created + installed packet space into the connection
// owner. Given the packet space (back-pointer/level already written), the
// connection whose slot `lvl` now holds it, and the untouched other slots,
// reassemble a full `connection_owner`. Reuses `restore_connection_owner`.
ghost fn deposit
  (#ps_v: PS.struct_packet_space)
  (#conn_v: C.struct_connection)
  (#old_pk: packets_t)
  (ps: ref PS.struct_packet_space)
  (conn: ref C.struct_connection)
  (lvl: U32.t)
  requires R.pts_to ps ps_v
  requires R.pts_to conn conn_v
  requires other_slots (CR.ref_to_core conn) old_pk (U32.v lvl)
  requires pure (
     (conn_of ps_v) == CR.ref_to_core conn
     /\ (lvl_of ps_v) == lvl
     /\ (packets_of conn_v)
          == CA.array_spec_set old_pk (U32.v lvl) (Some ps)
     /\ U32.v lvl < 3
     /\ not (R.is_null ps))
  ensures connection_owner_exists ps
{
  other_slots_set_stable (CR.ref_to_core conn) old_pk (U32.v lvl) ps;
  // Re-key the residual slots and the connection allocation onto the focused
  // packet space's OWN projections (back-pointer + level), so that
  // `restore_connection_owner` yields exactly `connection_owner_exists`'s body
  // (coords == ps_v.connection / ps_v.encrypt_level). Each rewrite is a pure
  // equality already in scope: ref_to_core conn == ps_v.connection,
  // array_spec_set old_pk (v lvl) (Some ps) == conn_v.packets, lvl == ps_v level.
  rewrite (other_slots (CR.ref_to_core conn)
             (CA.array_spec_set old_pk (U32.v lvl) (Some ps)) (U32.v lvl))
       as (other_slots (conn_of ps_v)
             (packets_of conn_v)
             (U32.v (lvl_of ps_v)));
  rewrite (R.pts_to conn conn_v)
       as (R.pts_to (CR.core_to_ref C.struct_connection
                       (conn_of ps_v)) conn_v);
  restore_connection_owner ps ps_v
    (conn_of ps_v)
    (lvl_of ps_v)
    (packets_of conn_v) conn_v
}
