#include "pal.h"
#include <stdint.h>

// This test documents (and locks in) how src/pass/merge.rs behaves across
// the various ways a function's specification (_requires/_ensures) can be
// split between a forward declaration and its definition, or duplicated
// across two forward declarations with no definition at all.
//
// Summary of results (as of this test's creation):
//
//   1. decl_defn_same_specs           — decl + defn, IDENTICAL specs
//        => FAILS: "declaration and definition ... have differing
//           specifications". This is a bug: merge.rs's equality check
//           on the two specs compares full Ast<T> nodes (which include
//           source-location info), not just their logical/textual
//           content, so two textually-identical specs written at two
//           different source locations are wrongly treated as differing.
//
//   2. decl_defn_diff_specs           — decl + defn, genuinely DIFFERENT specs
//        => FAILS (expected/correct): a real conflict is reported.
//
//   3. decl_defn_specs_on_decl_only   — specs only on the decl, bare defn
//        => SUCCEEDS (correct): the standard pattern; the decl's specs are
//           copied onto the definition.
//
//   4. decl_defn_specs_on_defn_only   — bare decl, specs only on the defn
//        => FAILS (expected/correct): "definition ... has specifications,
//           but its declaration does not; specifications should be on the
//           declaration".
//
//   5. decl_decl_diff_specs           — two forward decls only (no defn),
//                                        genuinely DIFFERENT specs
//        => SUCCEEDS with NO diagnostic at all. merge.rs's Phase 1
//           dedup logic for identically-keyed declarations blindly keeps
//           whichever occurrence it processes last and silently discards
//           the other, with no check that they agree. This is a real gap:
//           two conflicting bare declarations of the same function are
//           never cross-checked.
//
//   6. decl_decl_one_sided_specs      — two forward decls only, one with
//                                        specs and one bare (no defn)
//        => SUCCEEDS with NO diagnostic, and the specs-bearing version is
//           always kept regardless of which one appears first in the
//           source. This is most likely not merge.rs's own doing, but
//           Clang's own attribute-merging across a function's
//           redeclaration chain: by the time PAL's frontend walks the
//           AST, both FunctionDecl nodes it sees already carry the same
//           (merged) specs.

// --- 1. decl + defn, identical specs => currently FAILS (the bug) ---
int32_t decl_defn_same_specs(int32_t x)
  _requires(x < 100)
  _ensures(return == x + 1);

int32_t decl_defn_same_specs(int32_t x)
  _requires(x < 100)
  _ensures(return == x + 1)
{
  return x + 1;
}

// --- 2. decl + defn, genuinely different specs => FAILS (expected) ---
int32_t decl_defn_diff_specs(int32_t x)
  _requires(x < 100)
  _ensures(return == x + 1);

int32_t decl_defn_diff_specs(int32_t x)
  _requires(x < 5)
  _ensures(return == x + 999)
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

// --- 4. bare decl, specs only on the defn => FAILS (expected) ---
int32_t decl_defn_specs_on_defn_only(int32_t x);

int32_t decl_defn_specs_on_defn_only(int32_t x)
  _requires(x < 100)
  _ensures(return == x + 1)
{
  return x + 1;
}

// --- 5. two forward decls only (no defn), different specs => SUCCEEDS,
//        no diagnostic; one version is silently kept, the other discarded.
int32_t decl_decl_diff_specs(int32_t x)
  _requires(x < 100)
  _ensures(return == x + 1);

int32_t decl_decl_diff_specs(int32_t x)
  _requires(x < 5)
  _ensures(return == x + 999);

// --- 6. two forward decls only (no defn), one with specs, one bare =>
//        SUCCEEDS, no diagnostic; the specs-bearing version is retained.
int32_t decl_decl_one_sided_specs(int32_t x)
  _requires(x < 100)
  _ensures(return == x + 1);

int32_t decl_decl_one_sided_specs(int32_t x);

