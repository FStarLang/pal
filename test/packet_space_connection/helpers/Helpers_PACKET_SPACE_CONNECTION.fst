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

let slot_at (pk: packets_t) (i: nat)
  : GTot (option (ref PS.struct_packet_space)) =
  CA.array_spec_get pk i

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
           ** pure (pv.PS.struct_packet_space__connection == br)

// Ownership of every slot EXCEPT the focused index `k`. With only three
// encryption levels this is a fixed three-way bundle; the focused slot's `if`
// collapses to `emp` because its ownership travels separately as `pts_to ps`.
let other_slots (br: CR.core_ref) (pk: packets_t) (k: nat) : slprop =
  (if k = 0 then emp else slot_owner br (slot_at pk 0))
  ** (if k = 1 then emp else slot_owner br (slot_at pk 1))
  ** (if k = 2 then emp else slot_owner br (slot_at pk 2))

// A connection owner focused on packet space `ps` (which lives in slot `lvl`).
// It retains: the focused packet space, the connection allocation (reached
// through the core reference `back_ref`), and every other slot.
//
// KEY DESIGN POINT (witness selection): the two *stable* coordinates of the
// focus — the connection back-pointer `back_ref` and the encryption level `lvl`
// — are EXPLICIT parameters, NOT projections of `ps_v`. This is what makes the
// owner robust under mutation of the focused packet space. If instead the
// connection address / `other_slots` were written as `core_to_ref
// ps_v.connection` / `other_slots ps_v.connection ... (v ps_v.encrypt_level)`,
// then when a caller re-establishes `exists* ps_v .... connection_owner ...`
// after writing scalar fields of `ps`, Pulse's higher-order unifier could bind
// `ps_v` from those argument positions to the STALE pre-write value (the one the
// trade was opened with) rather than from `pts_to ps ps_v`. The scalar
// postcondition (stated over `ps_v`) would then be checked against the wrong
// value and fail. Threading `back_ref`/`lvl` separately leaves `ps_v` appearing
// only in `pts_to ps ps_v`, so it is pinned uniquely to the current value; the
// `pure` clause still ties the coordinates back to `ps_v` for callers that need
// it.
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
                ps_v.PS.struct_packet_space__connection) conn_v
  ** other_slots back_ref pk (U32.v lvl)
  ** pure (ps_v.PS.struct_packet_space__connection == back_ref
           /\ ps_v.PS.struct_packet_space__encrypt_level == lvl
           /\ conn_v.C.struct_connection__packets == pk
           /\ slot_at pk (U32.v lvl) == Some ps
           /\ not (R.is_null ps))

// A complete owner, with the stable coordinates fixed to the focused packet
// space's own back-pointer / level. This is the natural INPUT shape for an owner
// that still holds a concrete `ps_v` (nothing has been mutated yet).
[@@pulse_unfold]
let connection_owner_exists (ps: ref PS.struct_packet_space) : slprop =
  exists* (ps_v: PS.struct_packet_space) (conn_v: C.struct_connection).
    connection_owner ps ps_v
      ps_v.PS.struct_packet_space__connection
      ps_v.PS.struct_packet_space__encrypt_level
      conn_v.C.struct_connection__packets
      conn_v

// The whiteboard capability, generalized to the array layout:
//
//   forall* ps_v. trade (pts_to ps ps_v) (connection_owner ps ps_v (back ps_v))
//
// `back` maps the *current* packet-space value to the connection value the
// owner still holds. Two immutable coordinates are pinned in the trade
// antecedent, forced by the layout:
//   * `back_ref`  fixes the _core_ref reverse slot (as in the single-slot
//     model), so an arbitrary quantified ps_v cannot redirect the core
//     reference to an unowned connection.
//   * `lvl` fixes the encryption level, i.e. WHICH array slot the packet space
//     occupies. Without it a mutated ps_v could name a different slot and the
//     forward link `slot_at conn_v.packets (v lvl) == Some ps` would break.
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
       ** pure (ps_v.PS.struct_packet_space__connection == back_ref
                /\ ps_v.PS.struct_packet_space__encrypt_level == lvl))
      (connection_owner ps ps_v back_ref lvl pk (back ps_v))

// Recombine the fixed connection allocation and the residual slots with a
// current focused packet-space value. With the coordinates threaded explicitly
// the fold is a direct match — no rewriting of projections is required.
ghost fn restore_connection_owner
  (ps: ref PS.struct_packet_space)
  (ps_v: PS.struct_packet_space)
  (back_ref: CR.core_ref)
  (lvl: U32.t)
  (pk: packets_t)
  (conn_v: C.struct_connection)
  requires R.pts_to ps ps_v
  requires pure (ps_v.PS.struct_packet_space__connection == back_ref
                 /\ ps_v.PS.struct_packet_space__encrypt_level == lvl
                 /\ conn_v.C.struct_connection__packets == pk)
  requires R.pts_to (CR.core_to_ref C.struct_connection back_ref) conn_v
  requires other_slots back_ref pk (U32.v lvl)
  requires pure (slot_at pk (U32.v lvl) == Some ps
                 /\ not (R.is_null ps))
  ensures connection_owner ps ps_v back_ref lvl pk conn_v
{
  rewrite (R.pts_to (CR.core_to_ref C.struct_connection back_ref) conn_v)
       as (R.pts_to (CR.core_to_ref C.struct_connection
                       ps_v.PS.struct_packet_space__connection) conn_v);
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
    ** pure (ps_v.PS.struct_packet_space__connection == back_ref
             /\ ps_v.PS.struct_packet_space__encrypt_level == lvl)
{
  unfold (connection_owner_exists ps);
  with ps_v conn_v. assert (
    connection_owner ps (reveal ps_v)
      (reveal ps_v).PS.struct_packet_space__connection
      (reveal ps_v).PS.struct_packet_space__encrypt_level
      (reveal conn_v).C.struct_connection__packets
      (reveal conn_v));
  unfold (connection_owner ps (reveal ps_v)
      (reveal ps_v).PS.struct_packet_space__connection
      (reveal ps_v).PS.struct_packet_space__encrypt_level
      (reveal conn_v).C.struct_connection__packets
      (reveal conn_v));
  intro (forall* (ps_v_out: PS.struct_packet_space).
    T.trade
      (R.pts_to ps ps_v_out
       ** pure (ps_v_out.PS.struct_packet_space__connection
                  == (reveal ps_v).PS.struct_packet_space__connection
                /\ ps_v_out.PS.struct_packet_space__encrypt_level
                  == (reveal ps_v).PS.struct_packet_space__encrypt_level))
      (connection_owner ps ps_v_out
        (reveal ps_v).PS.struct_packet_space__connection
        (reveal ps_v).PS.struct_packet_space__encrypt_level
        (reveal conn_v).C.struct_connection__packets
        ((fun _ -> reveal conn_v) ps_v_out)))
    #(
      R.pts_to
        (CR.core_to_ref C.struct_connection
           (reveal ps_v).PS.struct_packet_space__connection)
        (reveal conn_v)
      ** other_slots (reveal ps_v).PS.struct_packet_space__connection
           (reveal conn_v).C.struct_connection__packets
           (U32.v (reveal ps_v).PS.struct_packet_space__encrypt_level)
      ** pure (
           slot_at (reveal conn_v).C.struct_connection__packets
             (U32.v (reveal ps_v).PS.struct_packet_space__encrypt_level)
             == Some ps
           /\ not (R.is_null ps)))
    fn _ ps_v_out {
      restore_connection_owner
        ps
        ps_v_out
        ((reveal ps_v).PS.struct_packet_space__connection)
        ((reveal ps_v).PS.struct_packet_space__encrypt_level)
        ((reveal conn_v).C.struct_connection__packets)
        (reveal conn_v)
    };
  fold (packet_space_to_connection ps
    (fun _ -> reveal conn_v)
    (reveal ps_v).PS.struct_packet_space__connection
    (reveal ps_v).PS.struct_packet_space__encrypt_level
    (reveal conn_v).C.struct_connection__packets);
  introduce exists* (ps_v_out: PS.struct_packet_space)
    (back_ref_out: CR.core_ref)
    (lvl_out: U32.t) (pk_out: packets_t)
    (back_out: PS.struct_packet_space -> GTot C.struct_connection).
      R.pts_to ps ps_v_out
      ** packet_space_to_connection ps back_out back_ref_out lvl_out pk_out
      ** pure (ps_v_out.PS.struct_packet_space__connection == back_ref_out
               /\ ps_v_out.PS.struct_packet_space__encrypt_level == lvl_out)
    with (reveal ps_v)
         ((reveal ps_v).PS.struct_packet_space__connection)
         ((reveal ps_v).PS.struct_packet_space__encrypt_level)
         ((reveal conn_v).C.struct_connection__packets)
         (fun _ -> reveal conn_v)
}

// Spend the quantified capability: after the callee has mutated the focused
// packet space (keeping its core_ref and level stable) recover full ownership.
// The ensures binds `back_ref`/`lvl` as SEPARATE existentials (not projections
// of `ps_v`) so the returned owner stays decoupled — see `connection_owner`.
ghost fn consume_packet_space_trade (ps: ref PS.struct_packet_space)
  requires exists* (ps_v: PS.struct_packet_space)
    (back_ref: CR.core_ref)
    (lvl: U32.t) (pk: packets_t)
    (back: PS.struct_packet_space -> GTot C.struct_connection).
    packet_space_to_connection ps back back_ref lvl pk
    ** R.pts_to ps ps_v
    ** pure (ps_v.PS.struct_packet_space__connection == back_ref
             /\ ps_v.PS.struct_packet_space__encrypt_level == lvl)
  ensures exists* (ps_v: PS.struct_packet_space) (back_ref: CR.core_ref)
    (lvl: U32.t) (pk: packets_t) (conn_v: C.struct_connection).
    connection_owner ps ps_v back_ref lvl pk conn_v
{
  with ps_v back_ref lvl pk back. assert (
    packet_space_to_connection ps (reveal back) (reveal back_ref) (reveal lvl)
      (reveal pk)
    ** R.pts_to ps (reveal ps_v)
    ** pure ((reveal ps_v).PS.struct_packet_space__connection == (reveal back_ref)
             /\ (reveal ps_v).PS.struct_packet_space__encrypt_level == (reveal lvl)));
  unfold (packet_space_to_connection ps (reveal back) (reveal back_ref) (reveal lvl)
    (reveal pk));
  Pulse.Lib.Forall.elim_forall (reveal ps_v);
  T.elim_trade
    (R.pts_to ps (reveal ps_v)
     ** pure ((reveal ps_v).PS.struct_packet_space__connection == (reveal back_ref)
              /\ (reveal ps_v).PS.struct_packet_space__encrypt_level == (reveal lvl)))
    (connection_owner ps (reveal ps_v) (reveal back_ref) (reveal lvl) (reveal pk)
       ((reveal back) (reveal ps_v)));
  introduce exists* (ps_v_out: PS.struct_packet_space)
    (back_ref_out: CR.core_ref) (lvl_out: U32.t) (pk_out: packets_t)
    (conn_v_out: C.struct_connection).
      connection_owner ps ps_v_out back_ref_out lvl_out pk_out conn_v_out
    with (reveal ps_v) (reveal back_ref) (reveal lvl) (reveal pk)
         ((reveal back) (reveal ps_v))
}
