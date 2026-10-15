module Helpers_PACKET_SPACE_CONNECTION

(* The Palow port of `Helpers_PACKET_SPACE_CONNECTION`.

   Same theory, and deliberately the same names, so the two can be read side by
   side. What is gone is the encoding:

   - `Pulse.Lib.C.CoreRef` disappears. A `_core_ref` existed because the old
     model gave a pointer a different type depending on how it was used, so a
     back-pointer into a struct that nobody owns needed a proof-only `core_ref`
     and a `core_to_ref` to turn it back into something a `pts_to` could name.
     In Palow every pointer is a `ptr`, so the back-pointer is simply the field
     value and `struct_connection_pts_to (conn_of ps_v)` is directly sayable.
     Three `rewrite`s in the old module exist only to move between `back_ref`
     and `core_to_ref back_ref`; two of them are gone here.

   - `Pulse.Lib.C.Array.array_spec` disappears. The old model gave a fixed
     array field a spec carrying a length, an initialisation mask and an
     `option` per slot, so reading a slot gave `option (ref ...)` and writing
     one needed `array_spec_set` alongside PAL's own `array_spec_upd` -- plus a
     lemma proving the two extensionally equal. In Palow a fixed array field is
     a `Seq.seq ptr` refined to its length, a slot is `Seq.index`, and a write
     is `Seq.upd`. `slot_at_set_ne` becomes `Seq.lemma_index_upd2` and
     `array_spec_upd_set_eq` is not needed at all.

   The absence of a NULL slot is spelled `is_null`, exactly as the C means it,
   rather than as `None` in an option layered on top of a null pointer. *)

#lang-pulse
open Pulse
open Pulse.Lib.C.Palow.Bytes
open Pulse.Lib.C.Palow.Ptr
open Pulse.Lib.C.Palow
open Pulse.Lib.C.Palow.Scalar
open Pulse.Lib.C.Palow.CTypes
open Pulse.Lib.C.Palow.Array
open Struct_connection
open Struct_packet_space
module T = Pulse.Lib.Trade
module U32 = FStar.UInt32
module Seq = FStar.Seq

(* The `packets` field's value. A Palow fixed array field is a sequence with its
   length in the type, so this is the field's type verbatim. *)
let packets_t = (s: Seq.seq ptr { Seq.length s == 3 })

unfold let conn_of (v: struct_packet_space) = v.fld_connection
unfold let lvl_of (v: struct_packet_space) = v.fld_encrypt_level
unfold let packets_of (v: struct_connection) = v.fld_packets

(* Total, so that a `pure` conjunction can mention a slot and its index bound
   in either order: F\* types the conjuncts before it has the earlier ones as
   hypotheses, so a partial `slot_at` makes the bound unusable where it is
   stated alongside the fact that needs it. *)
let slot_at (pk: packets_t) (i: nat) : GTot ptr =
  if i < 3 then Seq.index pk i else null

(* Total for the same reason, and additionally because an `ensures` is typed
   without its `requires` in scope, so a bound stated as a precondition cannot
   justify a `Seq.upd` in the postcondition. *)
let slot_set (pk: packets_t) (i: nat) (x: ptr) : GTot packets_t =
  if i < 3 then Seq.upd pk i x else pk

let slot_at_set (pk: packets_t) (i j: nat) (x: ptr)
  : Lemma (slot_at (slot_set pk i x) j == (if i = j && i < 3 then x else slot_at pk j))
          [SMTPat (slot_at (slot_set pk i x) j)]
  = if i < 3 && j < 3 then
      (if i = j then Seq.lemma_index_upd1 pk i x
       else Seq.lemma_index_upd2 pk i x j)

(* Ownership of the packet space a slot points at. A NULL slot owns nothing; a
   live slot owns its whole packet space and pins the back-pointer to the owning
   connection `br`. In the old model `br` was a `core_ref`; here it is the
   address itself. *)
let slot_owner (br: ptr) (o: ptr) : slprop =
  if is_null o then emp
  else exists* (pv: struct_packet_space).
         struct_packet_space_pts_to o 1.0R pv ** pure (conn_of pv == br)

(* Ownership of every slot except the focused index `k`, whose contribution is
   `emp` because its packet space travels separately. Three encryption levels,
   so a fixed three-way bundle. *)
let slot_owner_at (br: ptr) (pk: packets_t) (k j: nat) : slprop =
  if k = j || j >= 3 then emp else slot_owner br (slot_at pk j)

let other_slots (br: ptr) (pk: packets_t) (k: nat) : slprop =
  slot_owner_at br pk k 0 ** slot_owner_at br pk k 1 ** slot_owner_at br pk k 2

(* A connection owner focused on packet space `ps`, which lives in slot `lvl`.
   It retains the focused packet space, the connection allocation reached
   through the back-pointer, and every other slot.

   The two *stable* coordinates of the focus -- `back_ref` and `lvl` -- are
   explicit parameters rather than projections of `ps_v`, so that `ps_v` appears
   only in the packet space's own points-to and Pulse's unifier cannot bind it
   to a stale pre-write value. *)
[@@pulse_unfold]
let connection_owner
  (ps: ptr)
  (ps_v: struct_packet_space)
  (back_ref: ptr)
  (lvl: U32.t)
  (pk: packets_t)
  (conn_v: struct_connection)
  : slprop =
  struct_packet_space_pts_to ps 1.0R ps_v
  ** struct_connection_pts_to (conn_of ps_v) 1.0R conn_v
  ** other_slots back_ref pk (U32.v lvl)
  ** pure (conn_of ps_v == back_ref
           /\ lvl_of ps_v == lvl
           /\ packets_of conn_v == pk
           /\ U32.v lvl < 3
           /\ slot_at pk (U32.v lvl) == ps
           /\ not (is_null ps))

(* A complete owner with the stable coordinates fixed to the focused packet
   space's own back-pointer and level: the natural input shape for an owner that
   still holds a concrete `ps_v`. *)
[@@pulse_unfold]
let connection_owner_exists (ps: ptr) : slprop =
  exists* (ps_v: struct_packet_space) (conn_v: struct_connection).
    connection_owner ps ps_v
      (conn_of ps_v)
      (lvl_of ps_v)
      (packets_of conn_v)
      conn_v

(* The capability, quantified over the packet space's current value:

     forall* ps_v. trade (pts_to ps ps_v) (connection_owner ps ps_v ...)

   Quantifying over `ps_v` is what keeps the packet space mutable while it is
   borrowed. The antecedent pins the two immutable coordinates, so an arbitrary
   `ps_v` cannot redirect the back-pointer or name a different slot. *)
let packet_space_to_connection
  (ps: ptr)
  (back: struct_packet_space -> GTot struct_connection)
  (back_ref: ptr)
  (lvl: U32.t)
  (pk: packets_t)
  : slprop =
  forall* (ps_v: struct_packet_space).
    T.trade
      (struct_packet_space_pts_to ps 1.0R ps_v
       ** pure (conn_of ps_v == back_ref /\ lvl_of ps_v == lvl))
      (connection_owner ps ps_v back_ref lvl pk (back ps_v))

(* Recombine the connection allocation and the residual slots with a current
   focused packet-space value.

   The old model needed a `rewrite` here to re-key the connection allocation
   from `back_ref` onto `core_to_ref (conn_of ps_v)`. Palow needs it too --
   Pulse's matcher does not consult SMT for a slprop's arguments -- but it is a
   rewrite between two `ptr`s that are equal by the `pure` clause, with no
   coercion in the middle. *)
ghost fn restore_connection_owner
  (ps: ptr)
  (ps_v: struct_packet_space)
  (back_ref: ptr)
  (lvl: U32.t)
  (pk: packets_t)
  (conn_v: struct_connection)
  requires struct_packet_space_pts_to ps 1.0R ps_v
  requires pure (conn_of ps_v == back_ref
                 /\ lvl_of ps_v == lvl
                 /\ packets_of conn_v == pk
                 /\ U32.v lvl < 3)
  requires struct_connection_pts_to back_ref 1.0R conn_v
  requires other_slots back_ref pk (U32.v lvl)
  requires pure (slot_at pk (U32.v lvl) == ps /\ not (is_null ps))
  ensures connection_owner ps ps_v back_ref lvl pk conn_v
{
  rewrite (struct_connection_pts_to back_ref 1.0R conn_v)
       as (struct_connection_pts_to (conn_of ps_v) 1.0R conn_v);
  fold (connection_owner ps ps_v back_ref lvl pk conn_v)
}

(* An owner mints the capability from its complete root: capture the
   back-pointer and the level as the immutable coordinates, fix `back` to the
   owned connection value, and rebuild every trade instance from the single
   residual plus that instance's focused ownership. *)
ghost fn create_packet_space_trade (ps: ptr)
  requires connection_owner_exists ps
  ensures exists* (ps_v: struct_packet_space) (back_ref: ptr)
    (lvl: U32.t) (pk: packets_t)
    (back: struct_packet_space -> GTot struct_connection).
    struct_packet_space_pts_to ps 1.0R ps_v
    ** packet_space_to_connection ps back back_ref lvl pk
    ** pure (conn_of ps_v == back_ref /\ lvl_of ps_v == lvl)
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
  intro (forall* (ps_v_out: struct_packet_space).
    T.trade
      (struct_packet_space_pts_to ps 1.0R ps_v_out
       ** pure (conn_of ps_v_out == conn_of (reveal ps_v)
                /\ lvl_of ps_v_out == lvl_of (reveal ps_v)))
      (connection_owner ps ps_v_out
        (conn_of (reveal ps_v))
        (lvl_of (reveal ps_v))
        (packets_of (reveal conn_v))
        ((fun _ -> reveal conn_v) ps_v_out)))
    #(
      struct_connection_pts_to (conn_of (reveal ps_v)) 1.0R (reveal conn_v)
      ** other_slots (conn_of (reveal ps_v))
           (packets_of (reveal conn_v))
           (U32.v (lvl_of (reveal ps_v)))
      ** pure (
           slot_at (packets_of (reveal conn_v))
             (U32.v (lvl_of (reveal ps_v)))
             == ps
           /\ U32.v (lvl_of (reveal ps_v)) < 3
           /\ not (is_null ps)))
    fn _ ps_v_out {
      restore_connection_owner
        ps
        ps_v_out
        (conn_of (reveal ps_v))
        (lvl_of (reveal ps_v))
        (packets_of (reveal conn_v))
        (reveal conn_v)
    };
  fold (packet_space_to_connection ps
    (fun _ -> reveal conn_v)
    (conn_of (reveal ps_v))
    (lvl_of (reveal ps_v))
    (packets_of (reveal conn_v)));
}

(* Spend the capability: after the callee has mutated the focused packet space,
   keeping its back-pointer and level stable, recover full ownership.

   `ps_v` is an implicit parameter rather than an existential of the `ensures`,
   so the caller keeps knowing exactly which packet-space value it gets back --
   in particular the scalar fields it wrote just before calling. *)
ghost fn consume_packet_space_trade
  (#ps_v: struct_packet_space)
  (ps: ptr)
  requires exists* (back_ref: ptr)
    (lvl: U32.t) (pk: packets_t)
    (back: struct_packet_space -> GTot struct_connection).
    packet_space_to_connection ps back back_ref lvl pk
    ** struct_packet_space_pts_to ps 1.0R ps_v
    ** pure (conn_of ps_v == back_ref /\ lvl_of ps_v == lvl)
  ensures exists* (back_ref: ptr)
    (lvl: U32.t) (pk: packets_t) (conn_v: struct_connection).
    connection_owner ps ps_v back_ref lvl pk conn_v
{
  with back_ref lvl pk back. assert (
    packet_space_to_connection ps (reveal back) (reveal back_ref) (reveal lvl)
      (reveal pk)
    ** struct_packet_space_pts_to ps 1.0R ps_v
    ** pure (conn_of ps_v == reveal back_ref /\ lvl_of ps_v == reveal lvl));
  unfold (packet_space_to_connection ps (reveal back) (reveal back_ref)
    (reveal lvl) (reveal pk));
  Pulse.Lib.Forall.elim_forall ps_v;
  T.elim_trade
    (struct_packet_space_pts_to ps 1.0R ps_v
     ** pure (conn_of ps_v == reveal back_ref /\ lvl_of ps_v == reveal lvl))
    (connection_owner ps ps_v (reveal back_ref) (reveal lvl) (reveal pk)
       ((reveal back) ps_v));
}

(* ==========================================================================
   Create + install lifecycle (models QuicPacketSpaceInitialize).

   The theory above is borrow and return of an already-owned focused packet
   space. Initialisation is a different lifecycle: it turns a connection whose
   target slot is NULL into a full owner of a freshly created packet space in
   that slot.
   ========================================================================== *)

(* The pre-state of initialisation: the connection is owned by value, the target
   slot is NULL and so owns nothing, and every other slot is already owned. The
   back-pointer coordinate is the connection's own address, which is what the
   fresh packet space will store. *)
[@@pulse_unfold]
let connection_slot_empty (conn: ptr) (lvl: U32.t) : slprop =
  exists* (conn_v: struct_connection).
    struct_connection_pts_to conn 1.0R conn_v
    ** other_slots conn (packets_of conn_v) (U32.v lvl)
    ** pure (U32.v lvl < 3
             /\ is_null (slot_at (packets_of conn_v) (U32.v lvl)))

(* Writing slot `k` leaves slot `j`'s ownership untouched: for `j <> k` the two
   sides are the same `slot_owner`, because `Seq.upd` agrees with the original
   off `k`; for `j = k` both sides are `emp`. In the old model this needed a
   bespoke `array_spec_set` lemma with an SMT pattern. *)
ghost fn slot_owner_at_set_stable
  (br: ptr) (pk: packets_t) (k j: nat) (newptr: ptr)
  requires slot_owner_at br pk k j
  ensures slot_owner_at br (slot_set pk k newptr) k j
{
  rewrite (slot_owner_at br pk k j)
       as (slot_owner_at br (slot_set pk k newptr) k j)
}

ghost fn other_slots_set_stable
  (br: ptr) (pk: packets_t) (i: nat) (newptr: ptr)
  requires other_slots br pk i
  ensures other_slots br (slot_set pk i newptr) i
{
  unfold (other_slots br pk i);
  slot_owner_at_set_stable br pk i 0 newptr;
  slot_owner_at_set_stable br pk i 1 newptr;
  slot_owner_at_set_stable br pk i 2 newptr;
  fold (other_slots br (slot_set pk i newptr) i)
}

(* Deposit the freshly created and installed packet space into the connection
   owner: given the packet space with its back-pointer and level written, the
   connection whose slot `lvl` now holds it, and the untouched other slots,
   reassemble a full `connection_owner`. *)
ghost fn deposit
  (#ps_v: struct_packet_space)
  (#conn_v: struct_connection)
  (#old_pk: packets_t)
  (ps: ptr)
  (conn: ptr)
  (lvl: U32.t)
  requires struct_packet_space_pts_to ps 1.0R ps_v
  requires struct_connection_pts_to conn 1.0R conn_v
  requires other_slots conn old_pk (U32.v lvl)
  requires pure (
     conn_of ps_v == conn
     /\ lvl_of ps_v == lvl
     /\ packets_of conn_v == slot_set old_pk (U32.v lvl) ps
     /\ U32.v lvl < 3
     /\ not (is_null ps))
  ensures connection_owner_exists ps
{
  other_slots_set_stable conn old_pk (U32.v lvl) ps;
  rewrite (struct_connection_pts_to conn 1.0R conn_v)
       as (struct_connection_pts_to (conn_of ps_v) 1.0R conn_v);
  rewrite (other_slots conn (slot_set old_pk (U32.v lvl) ps) (U32.v lvl))
       as (other_slots (conn_of ps_v)
             (packets_of conn_v)
             (U32.v (lvl_of ps_v)));
  restore_connection_owner ps ps_v
    (conn_of ps_v)
    (lvl_of ps_v)
    (packets_of conn_v) conn_v
}
