module Helpers_PACKET_SPACE_CONNECTION

open Pulse
open Pulse.Lib.C
#lang-pulse

module C = Struct_connection
module PS = Struct_packet_space
module R = Pulse.Lib.Reference
module T = Pulse.Lib.Trade
module CR = Pulse.Lib.C.CoreRef

// A connection owner retains both separately allocated objects. The packet-space
// back-pointer is a core_ref, so CoreRef.core_to_ref recovers the connection
// allocation address. The selected connection.packet_space slot is ordinary and
// therefore uses a direct equality to ps.
[@@pulse_unfold]
let connection_owner
  (ps: ref PS.struct_packet_space)
  (ps_v: PS.struct_packet_space)
  (conn_v: C.struct_connection)
  : slprop =
  R.pts_to ps ps_v
  ** R.pts_to
       (CR.core_to_ref C.struct_connection
          ps_v.PS.struct_packet_space__connection)
       conn_v
  ** pure (conn_v.C.struct_connection__packet_space == ps)

[@@pulse_unfold]
let connection_owner_exists (ps: ref PS.struct_packet_space) : slprop =
  exists* (ps_v: PS.struct_packet_space) (conn_v: C.struct_connection).
    connection_owner ps ps_v conn_v

// The whiteboard capability:
//
//   forall* ps_v. trade (pts_to ps ps_v) (connection_owner ps ps_v (back ps_v))
//
// `back` is a ghost function mapping the *current* packet-space value to the
// connection value the owner still holds. Quantifying over ps_v is what lets the
// packet space be mutated before the trade is spent: unlike a monomorphic trade
// (which pins one pre-mutation ps_v in its antecedent and thereby forces the
// packet space to be const), this family carries one trade per ps_v and only the
// one whose antecedent `pts_to ps ps_v` the caller can supply is ever fired.
//
// The single unavoidable deviation from the whiteboard form is the `back_ref`
// parameter and the `pure (ps_v.connection == back_ref)` conjunct. It is forced
// by the real _core_ref layout: `connection_owner` locates the connection
// through the reverse field `ps_v.connection`, so without pinning that field to
// the captured allocation an arbitrary quantified ps_v would redirect the core
// reference to an unowned connection and `create_packet_space_trade` becomes
// unprovable.
let packet_space_to_connection
  (ps: ref PS.struct_packet_space)
  (back: PS.struct_packet_space -> GTot C.struct_connection)
  (back_ref: CR.core_ref)
  : slprop =
  forall* (ps_v: PS.struct_packet_space).
    T.trade
      (R.pts_to ps ps_v
       ** pure (ps_v.PS.struct_packet_space__connection == back_ref))
      (connection_owner ps ps_v (back ps_v))

// Recombine the fixed connection allocation with a current packet-space value
// once the core_ref equality has identified their addresses.
ghost fn restore_connection_owner
  (ps: ref PS.struct_packet_space)
  (ps_v: PS.struct_packet_space)
  (back_ref: CR.core_ref)
  (conn_v: C.struct_connection)
  requires R.pts_to ps ps_v
  requires pure (ps_v.PS.struct_packet_space__connection == back_ref)
  requires R.pts_to (CR.core_to_ref C.struct_connection back_ref) conn_v
  requires pure (conn_v.C.struct_connection__packet_space == ps)
  ensures connection_owner ps ps_v conn_v
{
  rewrite each (CR.core_to_ref C.struct_connection back_ref)
    as (CR.core_to_ref C.struct_connection
      ps_v.PS.struct_packet_space__connection);
  fold (connection_owner ps ps_v conn_v)
}

// An owner creates the capability from its complete root. It captures the
// immutable core_ref as back_ref and fixes the ghost `back` function to the
// owned connection value. The forall* introduction builds every trade instance
// from that single residual connection allocation and the instance's current
// packet-space ownership; the `pure` premise supplies the core_ref equality each
// instance needs.
ghost fn create_packet_space_trade (ps: ref PS.struct_packet_space)
  requires connection_owner_exists ps
  ensures exists* (ps_v: PS.struct_packet_space) (back_ref: CR.core_ref)
    (back: PS.struct_packet_space -> GTot C.struct_connection).
    R.pts_to ps ps_v
    ** packet_space_to_connection ps back back_ref
    ** pure (ps_v.PS.struct_packet_space__connection == back_ref)
{
  unfold (connection_owner_exists ps);
  with ps_v conn_v. assert (connection_owner ps (reveal ps_v) (reveal conn_v));
  unfold (connection_owner ps (reveal ps_v) (reveal conn_v));
  intro (forall* (ps_v_out: PS.struct_packet_space).
    T.trade
      (R.pts_to ps ps_v_out
       ** pure (ps_v_out.PS.struct_packet_space__connection
                == (reveal ps_v).PS.struct_packet_space__connection))
      (connection_owner ps ps_v_out ((fun _ -> reveal conn_v) ps_v_out)))
    #(
      R.pts_to
        (CR.core_to_ref C.struct_connection
           (reveal ps_v).PS.struct_packet_space__connection)
        (reveal conn_v)
      ** pure ((reveal conn_v).C.struct_connection__packet_space == ps))
    fn _ ps_v_out {
      restore_connection_owner
        ps
        ps_v_out
        ((reveal ps_v).PS.struct_packet_space__connection)
        (reveal conn_v)
    };
  fold (packet_space_to_connection ps
    (fun _ -> reveal conn_v)
    (reveal ps_v).PS.struct_packet_space__connection);
  introduce exists* (ps_v_out: PS.struct_packet_space)
    (back_ref_out: CR.core_ref)
    (back_out: PS.struct_packet_space -> GTot C.struct_connection).
      R.pts_to ps ps_v_out
      ** packet_space_to_connection ps back_out back_ref_out
      ** pure (ps_v_out.PS.struct_packet_space__connection == back_ref_out)
    with (reveal ps_v)
         ((reveal ps_v).PS.struct_packet_space__connection)
         (fun _ -> reveal conn_v)
}

// This consumer combines PAL's automatic consumed packet-space ownership with
// the one separate quantified capability. It instantiates the capability only
// after receiving the current packet-space value and proving that its core_ref
// still equals the captured back-pointer.
ghost fn consume_packet_space_trade (ps: ref PS.struct_packet_space)
  requires exists* (ps_v: PS.struct_packet_space)
    (back_ref: CR.core_ref)
    (back: PS.struct_packet_space -> GTot C.struct_connection).
    packet_space_to_connection ps back back_ref
    ** R.pts_to ps ps_v
    ** pure (ps_v.PS.struct_packet_space__connection == back_ref)
  ensures exists* (ps_v: PS.struct_packet_space) (conn_v: C.struct_connection).
    connection_owner ps ps_v conn_v
{
  with ps_v back_ref back. assert (
    packet_space_to_connection ps (reveal back) (reveal back_ref)
    ** R.pts_to ps (reveal ps_v)
    ** pure ((reveal ps_v).PS.struct_packet_space__connection
             == (reveal back_ref)));
  unfold (packet_space_to_connection ps (reveal back) (reveal back_ref));
  Pulse.Lib.Forall.elim_forall (reveal ps_v);
  T.elim_trade
    (R.pts_to ps (reveal ps_v)
     ** pure ((reveal ps_v).PS.struct_packet_space__connection
              == (reveal back_ref)))
    (connection_owner ps (reveal ps_v) ((reveal back) (reveal ps_v)));
  introduce exists* (ps_v_out: PS.struct_packet_space)
    (conn_v_out: C.struct_connection).
      connection_owner ps ps_v_out conn_v_out
    with (reveal ps_v) ((reveal back) (reveal ps_v))
}
