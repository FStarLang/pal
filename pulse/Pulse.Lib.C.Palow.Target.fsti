module Pulse.Lib.C.Palow.Target

(* ---------------------------------------------------------------------------
   The target machine, left abstract.

   The library is proved for every target at once: nothing here says what the
   target is, so nothing that depends on it can be proved from the library
   alone. A generated module that is translated for one concrete target states
   which one it is with a top-level `assume` in its implementation (never in
   its interface, so the assumption does not reach the modules that use it);
   a module translated for no particular target states nothing, and what it
   proves holds on all of them. See `palow.md`.
   --------------------------------------------------------------------------- *)

(* Whether a scalar's object representation puts its least significant byte at
   the lowest address. *)
val little_endian : bool
