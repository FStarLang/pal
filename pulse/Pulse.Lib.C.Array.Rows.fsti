module Pulse.Lib.C.Array.Rows
open Pulse
open Pulse.Lib.C.Array
module SZ = FStar.SizeT

#lang-pulse

/// ---------------------------------------------------------------------------
/// Rows of a multidimensional C array.
///
/// THIS MODULE IS AXIOMATIC. Every `val` below is assumed, not proved. It is
/// the smallest statement of a fact about the C memory model that
/// `Pulse.Lib.C.Array`'s representation cannot express, and it is kept in its
/// own module so that the trusted surface it adds is a single `grep` away.
///
/// ## The fact
///
/// In C, `T a[M][N]` is M*N elements of `T` laid out contiguously, and `a[i]`
/// is an array of N elements of `T` starting at `a + i*N`. A row *is* memory.
///
/// ## Why it has to be assumed
///
/// `Pulse.Lib.C.Array` models `T a[M][N]` as
///
///     array (full_array_lspec T N)
///
/// -- an array of M **ghost row values** (`array_spec` is a `Seq.seq` of
/// spec cells; see `Pulse.Lib.C.Array.fst`), not M rows of memory. Under that
/// model the inner row has no address at all, so there is nothing to prove
/// `array_borrow_row` *from*: `array_spec_idx s i` yields a pure spec, and no
/// rule takes a spec to an `array` handle. The gap is in the model, not in the
/// lemma library -- `array_spec_borrow`, `array_spec_set` and friends all
/// already exist and are used unchanged below.
///
/// The principled alternative is to flatten: model `T a[M][N]` as a single
/// `array T` of length `M*N` and lower `a[i][j]` to `a[i*N + j]`. That is
/// exact and would need no axiom, but it changes the type PAL gives every
/// multidimensional object, and so touches struct predicates, globals and
/// annotations alike. This module is the cheap, honest interim: it says
/// exactly what the flattened model would prove, and no more.
///
/// ## What is NOT assumed
///
/// * Nothing about bounds. `array_borrow_row` requires the row index to be
///   in the mask and initialized, so an out-of-range row is still a proof
///   obligation the caller has to discharge.
/// * No aliasing between distinct rows is claimed or needed: a borrowed row is
///   carved out of the parent's mask with the *existing* `array_spec_borrow`,
///   so the parent demonstrably no longer owns it and two rows cannot be
///   borrowed onto the same memory.
/// * Nothing about permissions. The borrow takes full permission, exactly as
///   `array_borrow_cell` does.
///
/// Recorded as PAL_LIMITATIONS.md L30 in the FunOS coco tree.
/// ---------------------------------------------------------------------------

/// The handle for row `i` of `a`. In C this is pure address arithmetic
/// (`a + i*N`); here it is ghost, and exists only to *name* the borrowed row
/// across the borrow/return boundary -- the same role `array_cell_ref` plays
/// for a single cell.
val array_row_ref (#t: Type u#a) (#n: nat)
                  (a: array (full_array_lspec t n)) (i: nat)
  : GTot (array t)

/// Distinct rows of the same array are distinct handles. Without this, two
/// borrows of different rows cannot be told apart in a proof context, and
/// `array_return_row` could return a row to the wrong index.
val array_row_ref_inj (#t: Type u#a) (#n: nat)
                      (a: array (full_array_lspec t n)) (i: nat) (j: nat)
  : Lemma (requires i <> j)
          (ensures array_row_ref a i =!= array_row_ref a j)

/// Borrow row `i` of `a` as a real `array t`, carving it out of `a`'s mask.
/// The row is handed out at its current spec value, which the parent's
/// `full_array_lspec` element type guarantees is itself full.
///
/// This is the row analogue of `array_borrow_cell`, and it uses the same mask
/// bookkeeping (`array_spec_borrow`) -- only the ref-to-array step is new, and
/// that step is the assumption.
val array_borrow_row (#t: Type u#a) (#n: nat)
                     (a: array (full_array_lspec t n)) (i: SZ.t)
                     (#s: erased (array_spec (full_array_lspec t n))
                          { array_spec_initd s (SZ.v i) /\ array_spec_mask s (SZ.v i) })
  : stt (array t)
        (array_pts_to a 1.0R s)
        (fun r -> array_pts_to r 1.0R (array_spec_idx s (SZ.v i))
               ** array_pts_to a 1.0R (array_spec_borrow s (SZ.v i))
               ** rewrites_to r (array_row_ref a (SZ.v i)))

/// Give a borrowed row back, writing its (possibly updated) value into the
/// parent. The index is left implicit so that a row borrowed at a symbolic
/// index can be returned, exactly as for `array_return_cell`.
val array_return_row (#t: Type u#a) (#n: nat)
                     (a: array (full_array_lspec t n))
                     (#i: nat)
                     (#w: full_array_lspec t n)
                     (#s: erased (array_spec (full_array_lspec t n))
                          { array_spec_mask s i })
  : stt_ghost unit emp_inames
      (array_pts_to (array_row_ref a i) 1.0R w
        ** array_pts_to a 1.0R (array_spec_borrow s i))
      (fun _ -> array_pts_to a 1.0R (array_spec_set s i (Some w)))
