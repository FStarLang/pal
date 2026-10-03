module Pulse.Lib.C.Palow.Target

(* ---------------------------------------------------------------------------
   The target's byte order, abstract to the library.

   Every scalar representation is `encode byte_order ...`, and the library is
   checked against this interface only, so no library proof can depend on the
   order: whatever it proves holds on every target.

   The implementation is not part of the library. `pal` writes it into
   `--outdir`, from the same clang `TargetInfo` that supplies every size,
   alignment and offset in the generated code, so the order and the layout
   come from one source and cannot disagree. Beside it `pal` writes
   `Pulse.Lib.C.Palow.TargetFacts`, which is the only way for a proof that
   needs the concrete order -- union punning, a byte array read as an integer,
   a wire format -- to learn it. See `palow.md`.
   --------------------------------------------------------------------------- *)

val byte_order : Pulse.Lib.C.Palow.Encoding.byte_order
