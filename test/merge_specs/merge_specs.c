#include "pal.h"
#include <stdint.h>

// This test documents how src/pass/merge.rs handles a function's
// specification (_requires/_ensures) when it is split between a forward
// declaration and its definition, or duplicated across two forward
// declarations with no definition at all.
//
// merge.rs compares specs *semantically* (via their pretty-printed form,
// ignoring source-location metadata) rather than with raw `==` on the
// underlying Ast<T> nodes, since two textually-identical specs written at
// different source locations would otherwise never compare equal. This
// comparison is applied consistently both for declaration-vs-definition
// specs and for declaration-vs-declaration specs (there's no reason for
// one of those two cases to be checked syntactically and the other
// semantically — the same location-leak issue affects both).
//
// Summary of results:
//
//   1. decl_defn_same_specs           — decl + defn, IDENTICAL specs
//        => SUCCEEDS: merges cleanly (see below, compiled).
//
//   2. decl_defn_diff_specs           — decl + defn, genuinely DIFFERENT
//                                        specs
//        => FAILS: "declaration and definition of X have differing
//           specifications" (a real conflict; not exercised in compiled
//           code here since this test is meant to pass cleanly).
//
//   3. decl_defn_specs_on_decl_only   — specs only on the decl, bare defn
//        => SUCCEEDS: the standard pattern; the decl's specs are copied
//           onto the definition (see below, compiled).
//
//   4. decl_defn_specs_on_defn_only   — bare decl, specs only on the defn
//        => FAILS: "definition of X has specifications, but its
//           declaration does not; specifications should be on the
//           declaration" (not exercised in compiled code here).
//
//   5. decl_decl_diff_specs           — two forward decls only (no defn),
//                                        genuinely DIFFERENT specs
//        => FAILS: "multiple declarations of X have differing
//           specifications" (not exercised in compiled code here).
//
//   6. decl_decl_one_sided_specs      — two forward decls only, one with
//                                        specs and one bare (no defn)
//        => SUCCEEDS: no diagnostic, and the specs-bearing version is
//           kept regardless of which one appears first in the source
//           (see below, compiled). This is most likely not merge.rs's own
//           doing, but Clang's own attribute-merging across a function's
//           redeclaration chain: by the time PAL's frontend walks the
//           AST, both FunctionDecl nodes it sees already carry the same
//           (merged) specs.

// --- 1. decl + defn, identical specs => SUCCEEDS ---
int32_t decl_defn_same_specs(int32_t x)
  _requires(x < 100)
  _ensures(return == x + 1);

int32_t decl_defn_same_specs(int32_t x)
  _requires(x < 100)
  _ensures(return == x + 1)
{
  return x + 1;
}

// --- 3. specs only on the decl, bare defn => SUCCEEDS ---
int32_t decl_defn_specs_on_decl_only(int32_t x)
  _requires(x < 100)
  _ensures(return == x + 1);

int32_t decl_defn_specs_on_decl_only(int32_t x)
{
  return x + 1;
}

// --- 6. two forward decls only (no defn), one with specs, one bare =>
//        SUCCEEDS, no diagnostic; the specs-bearing version is retained.
int32_t decl_decl_one_sided_specs(int32_t x)
  _requires(x < 100)
  _ensures(return == x + 1);

int32_t decl_decl_one_sided_specs(int32_t x);
