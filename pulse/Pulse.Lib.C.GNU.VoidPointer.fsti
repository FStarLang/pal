module Pulse.Lib.C.GNU.VoidPointer

open Pulse.Lib.C.CoreRef

(* GNU C void-pointer arithmetic uses byte offsets (element size 1):
   https://gcc.gnu.org/onlinedocs/gcc/Pointer-Arith.html

   An abstract raw-value operation, not an ISO C portability or memory-safety
   specification. Totality of this abstraction does not establish definedness
   of every concrete pointer computation. There are deliberately no address,
   non-nullness, injectivity, composition, or ownership laws. In particular,
   the result grants no right to dereference, access MMIO, or recover storage.

   PAL uses this only for void* +/- integer with the pointer on the left.
   The integer expression is evaluated in its source type before widening;
   subtraction negates the mathematical value, not a machine integer. *)
val core_offset (base: core_ref) (bytes: int) : Tot core_ref
