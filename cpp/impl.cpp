#include "generated.h"
#include "clang/Driver/Driver.h"
#include "clang/Frontend/FrontendActions.h"
#include "clang/Lex/MacroArgs.h"
#include "clang/Tooling/CompilationDatabase.h"
#include "clang/Tooling/Tooling.h"
#include <dlfcn.h>
#include <optional>
#include <sstream>
#include <unordered_set>
#include <vector>

using namespace clang;
using namespace clang::tooling;
using rust::Ref;
using rust::RefMut;
using rust::std::rc::Rc;
using rust::std::vec::Vec;
using namespace rust::pal::clang;
namespace ir = rust::pal::ir;
using OptExpr = rust::core::option::Option<Rc<ir::Expr>>;

llvm::StringRef toStringRef(Ref<rust::Str> str) {
  return llvm::StringRef((char const *)str.as_ptr(), str.len());
}

std::string toString(Ref<rust::Str> str) {
  return std::string((char const *)str.as_ptr(), str.len());
}

Ref<rust::Str> toStr(llvm::StringRef const &str) {
  return str_from_parts((uint8_t const *)str.data(), str.size());
}

Ref<rust::Str> toStr(std::string const &str) {
  return str_from_parts((uint8_t const *)str.data(), str.size());
}

// Returns true if `s` contains a `continue` that binds to the enclosing loop,
// i.e. a `continue` that is not nested inside another loop. Nested `for`,
// `while`, and `do-while` loops act as boundaries (their `continue` belongs to
// them), so we do not descend into them. A `switch` does NOT capture `continue`
// in C, so we descend into it (and into `if`, blocks, labels, etc.).
static bool hasTopLevelContinue(const Stmt *s) {
  if (!s)
    return false;
  if (isa<ContinueStmt>(s))
    return true;
  if (isa<ForStmt>(s) || isa<WhileStmt>(s) || isa<DoStmt>(s))
    return false;
  for (const Stmt *child : s->children())
    if (hasTopLevelContinue(child))
      return true;
  return false;
}

using SnipMap = rust::pal::hauntedc::SnippetMap;
using TargetIntWidths = rust::pal::hauntedc::TargetIntWidths;

template <> struct std::hash<FileID> {
  std::size_t operator()(FileID const &s) const noexcept {
    return s.getHashValue();
  }
};
struct RangeMap {
  RangeMap(RefMut<Ctx> &c) : ctx(c) {}
  RefMut<Ctx> ctx;
  std::unordered_map<FileID, Rc<rust::Str>> files;

  Rc<rust::Str> getFileName(SourceManager &sm, FileID id) {
    if (auto result = files.find(id); result != files.end()) {
      return result->second.clone();
    } else {
      rust::Ref<rust::Str> fn = "<unknown>"_rs;
      if (id.isValid()) {
        if (auto entryRef = sm.getFileEntryRefForID(id)) {
          fn = toStr(entryRef->getName());
        }
      }
      auto res = ctx.intern_str(fn);
      files[id] = res.clone();
      return res;
    }
  }

  Rc<ir::SourceInfo> getExpansionRange(SourceManager &sm, SourceRange range) {
    return mk_original_location(
        getFileName(sm, sm.getFileID(sm.getExpansionLoc(range.getBegin()))),
        sm.getExpansionLineNumber(range.getBegin()),
        sm.getExpansionColumnNumber(range.getBegin()),
        sm.getExpansionLineNumber(range.getEnd()),
        sm.getExpansionColumnNumber(range.getEnd()));
  }
};

class MacroTracker : public PPCallbacks {
public:
  MacroTracker(RangeMap &m, SnipMap &s, CompilerInstance &ci)
      : rangeMap(m), snippets(s), compilerInst(ci) {}
  RangeMap &rangeMap;
  SnipMap &snippets;
  CompilerInstance &compilerInst;

  void MacroExpands(Token const &MacroNameTok, MacroDefinition const &MD,
                    SourceRange Range, MacroArgs const *Args) override {
    auto &sm = compilerInst.getSourceManager();
    auto &langOpts = compilerInst.getLangOpts();
    if (Args) {
      InlineCodeBuilder toks = InlineCodeBuilder::new_();
      unsigned numArgs = Args->getNumMacroArguments();
      for (unsigned i = 0; i < numArgs; ++i) {
        Token const *argTokens = Args->getUnexpArgument(i);
        unsigned numTokens = Args->getArgLength(argTokens);

        for (unsigned j = 0; j < numTokens; ++j) {
          auto &tok = argTokens[j];
          std::string spelling = Lexer::getSpelling(tok, sm, langOpts);

          Rc<ir::SourceInfo> loc;
          SourceLocation tokLoc = sm.getSpellingLoc(tok.getLocation());
          if (auto fileID = sm.getFileID(tokLoc); fileID.isValid()) {
            unsigned beginLine = sm.getSpellingLineNumber(tokLoc);
            unsigned beginChar = sm.getSpellingColumnNumber(tokLoc);
            unsigned endLine = beginLine;
            unsigned endChar = beginChar + spelling.length();
            loc = mk_original_location(rangeMap.getFileName(sm, fileID),
                                       beginLine, beginChar, endLine, endChar);
          } else {
            auto expansionRange = sm.getExpansionRange(
                SourceRange(tok.getLocation(), tok.getEndLoc()));
            unsigned beginLine =
                sm.getExpansionLineNumber(expansionRange.getBegin());
            unsigned beginChar =
                sm.getExpansionColumnNumber(expansionRange.getBegin());
            unsigned endLine =
                sm.getExpansionLineNumber(expansionRange.getEnd());
            unsigned endChar =
                sm.getExpansionColumnNumber(expansionRange.getEnd());
            loc = mk_fallback_sourceinfo(mk_original_location(
                rangeMap.getFileName(sm,
                                     sm.getFileID(expansionRange.getBegin())),
                beginLine, beginChar, endLine, endChar));
          }

          Ref<rust::Str> before = tok.isAtStartOfLine()   ? "\n"_rs
                                  : tok.hasLeadingSpace() ? " "_rs
                                                          : ""_rs;
          toks.push_token(before, std::move(loc), toStr(spelling));
        }
      }
      unsigned ctr = compilerInst.getPreprocessor().getCounterValue();
      toks.insert_into_map(ctr, snippets);
    }
  }
};

Rc<rust::num_bigint::BigInt> toBigInt(llvm::APInt const &n) {
  llvm::SmallString<16> out;
  n.toStringSigned(out);
  return mk_bigint(toStr(out));
}

Rc<rust::num_bigint::BigInt> toBigInt(llvm::APSInt const &n) {
  llvm::SmallString<16> out;
  n.toString(out);
  return mk_bigint(toStr(out));
}

struct AnonNameGen {
  llvm::StringRef base;
  unsigned i = 0;

  AnonNameGen(llvm::StringRef b) : base(b) {}

  std::string next() {
    std::ostringstream out;
    out.write(base.data(), base.size());
    out << "_anon_" << ++i;
    return out.str();
  }
};

class PALConsumer : public ASTConsumer {
public:
  PALConsumer(RefMut<Ctx> c, RangeMap &m, SnipMap &s, CompilerInstance &ci)
      : ctx(c), rangeMap(m), snippets(s), sm(ci.getSourceManager()) {}

  RefMut<Ctx> ctx;
  RangeMap &rangeMap;
  SnipMap &snippets;
  SourceManager &sm;
  ASTContext *astCtx = nullptr;
  std::unordered_set<RecordDecl *>
      alreadyDefined; // guard against recursive structures
  std::unordered_map<RecordDecl *, std::string>
      structNames; // map record decls to generated struct names
  Expr *forLoopIncrement = nullptr;
  // When inside a switch desugaring, break sets this flag instead of mk_break
  Rc<ir::Ident> *switchBreakId = nullptr;

  // TODO: should probably wait with translation until after parsing

  void Initialize(ASTContext &Context) override {
    astCtx = &Context;
    auto const &TI = Context.getTargetInfo();
    ctx.set_target_int_widths(
        TargetIntWidths(TI.getCharWidth(), TI.getShortWidth(), TI.getIntWidth(),
                        TI.getLongWidth(), TI.getLongLongWidth()));
  }

  virtual bool HandleTopLevelDecl(DeclGroupRef DG) override {
    for (auto D : DG)
      HandleDecl(D);
    return ASTConsumer::HandleTopLevelDecl(DG);
  }

  Rc<ir::Ident> getDeclName(NamedDecl *d) {
    auto loc = mk_fallback_sourceinfo(
        getRange(d->getSourceRange())); // TODO: get range of name token
    return ctx.mk_ident(toStr(d->getName()), std::move(loc));
  }

  // Name to use for a struct/union field. Unnamed fields (e.g. C11 anonymous
  // struct/union members) have no identifier, so we synthesize a stable name
  // from the field's index within its record. The index is deterministic and
  // shared by the field definition and every member access referring to it, so
  // the synthesized names stay consistent across the whole translation.
  std::string fieldNameStr(FieldDecl const *f) {
    if (f->getIdentifier())
      return f->getName().str();
    return "_unnamed" + std::to_string(f->getFieldIndex());
  }

  RecordDecl *recordKey(RecordDecl *decl) {
    return cast<RecordDecl>(decl->getCanonicalDecl());
  }

  Rc<ir::SourceInfo> getRange(SourceRange const &range) {
    return rangeMap.getExpansionRange(sm, range);
  }

  template <typename T>
  void reportUnsupported(SourceRange const &rng, Rc<ir::SourceInfo> const &loc,
                         char const *msg, T const &extra) {
    if (!sm.isInMainFile(sm.getExpansionLoc(rng.getBegin()))) {
      // only complain about unsupported syntax in main file
      return;
    }
    ctx.report_diag(loc.clone(), true, toStr(std::string(msg) + extra));
  }

  // Translate a single struct/union field into the IR, pushing it onto the
  // given builder. Handles plain fields and unsigned bit-fields; rejects
  // signed bit-fields and skips anonymous/zero-width padding bit-fields.
  void addRecordField(DeclBuilder &builder, FieldDecl *f,
                      AnonNameGen *liftStructs, bool inUnion) {
    auto floc = getRange(f->getSourceRange());
    if (f->isBitField()) {
      // Anonymous / zero-width bit-fields are pure padding with no accessible
      // value; drop them entirely.
      if (f->isUnnamedBitField())
        return;
      // Bit-fields are only modeled inside structs; union bit-fields would need
      // the same value-based encoding layered on the union variant model.
      if (inUnion) {
        reportUnsupported(f->getSourceRange(), floc,
                          "unsupported bit-field in union", "");
        return;
      }
      // Only unsigned (and _Bool) bit-fields are modeled. Signed bit-fields
      // would need sign-extension on read and have implementation-defined
      // out-of-range write semantics (C11 6.3.1.3p3), so reject them.
      if (!f->getType()->isUnsignedIntegerType()) {
        reportUnsupported(
            f->getSourceRange(), floc,
            "unsupported signed bit-field (only unsigned bit-fields are "
            "supported)",
            "");
        return;
      }
      unsigned width = f->getBitWidthValue();
      builder.field_bitfield(
          ctx.mk_ident(toStr(fieldNameStr(f)), std::move(floc)),
          trQualType(f->getType(), f->getSourceRange(), liftStructs), width);
      return;
    }
    auto qt = f->getType();
    auto *qtPtr = qt.IgnoreParens().getTypePtr();
    if (auto *iat = dyn_cast<IncompleteArrayType>(qtPtr)) {
      // Flexible array member: `T name[]` as the last field of a struct (C11
      // 6.7.2.1). Clang guarantees it is the last field. Model it inline as an
      // unsized `array_spec T` in the noeq record; a `_refines(...)` clause on
      // the field supplies an optional length refinement.
      if (inUnion) {
        reportUnsupported(f->getSourceRange(), floc,
                          "unsupported flexible array member in union", "");
        return;
      }
      auto elemTy =
          trQualType(iat->getElementType(), f->getSourceRange(), liftStructs);
      builder.field(
          ctx.mk_ident(toStr(fieldNameStr(f)), std::move(floc)),
          trTypeAttrs(f->getAttrs(),
                      mk_flex_array_type(getRange(f->getSourceRange()),
                                         std::move(elemTy))));
    } else if (isa<VariableArrayType>(qtPtr)) {
      reportUnsupported(f->getSourceRange(), floc,
                        "unsupported non-constant-length array field", "");
    } else {
      builder.field(ctx.mk_ident(toStr(fieldNameStr(f)), std::move(floc)),
                    trTypeAttrs(f->getAttrs(),
                                trQualType(f->getType(), f->getSourceRange(),
                                           liftStructs)));
    }
  }

  void trRecordDecl(Rc<ir::Ident> ident, RecordDecl *decl,
                    AnonNameGen *liftStructs) {
    auto key = recordKey(decl);
    if (!decl->isCompleteDefinition()) {
      if (decl->getTagKind() == TagTypeKind::Struct) {
        auto loc = getRange(decl->getSourceRange());
        ctx.add_struct_decl(std::move(loc), std::move(ident));
      }
      return;
    }
    if (!alreadyDefined.insert(key).second)
      return;
    auto loc = getRange(decl->getSourceRange());
    auto builder = DeclBuilder::new_(loc.clone(), ident.clone());
    if (decl->getTagKind() == TagTypeKind::Struct) {
      // Check for struct-level attributes
      if (decl->hasAttrs()) {
        for (auto *attr : decl->getAttrs()) {
          if (auto *ann = dyn_cast<AnnotateAttr>(attr)) {
            if (ann->getAnnotation() == "pal-eager-unfold-predicate" &&
                ann->args_size() == 0) {
              builder.set_eager_unfold_pred();
            }
          }
        }
      }
      // Process nested record declarations (inner structs/unions)
      for (auto *D : decl->decls()) {
        if (auto *inner = dyn_cast<RecordDecl>(D)) {
          if (inner->isCompleteDefinition() && inner->getIdentifier()) {
            auto innerLoc = getRange(inner->getSourceRange());
            auto innerName =
                ctx.mk_ident(toStr(inner->getName()), innerLoc.clone());
            auto innerAnon = AnonNameGen(inner->getName());
            trRecordDecl(std::move(innerName), inner, &innerAnon);
          }
        }
      }
      for (auto f : decl->fields()) {
        addRecordField(builder, f, liftStructs, /*inUnion=*/false);
      }
      ctx.add_struct(std::move(builder));
    } else if (decl->getTagKind() == TagTypeKind::Union) {
      // Process nested record declarations (inner structs/unions)
      for (auto *D : decl->decls()) {
        if (auto *inner = dyn_cast<RecordDecl>(D)) {
          if (inner->isCompleteDefinition() && inner->getIdentifier()) {
            auto innerLoc = getRange(inner->getSourceRange());
            auto innerName =
                ctx.mk_ident(toStr(inner->getName()), innerLoc.clone());
            auto innerAnon = AnonNameGen(inner->getName());
            trRecordDecl(std::move(innerName), inner, &innerAnon);
          }
        }
      }
      for (auto f : decl->fields()) {
        addRecordField(builder, f, liftStructs, /*inUnion=*/true);
      }
      ctx.add_union(std::move(builder));
    } else {
      reportUnsupported(decl->getSourceRange(), loc, "unsupported record kind",
                        "");
    }
  }

  Rc<ir::Type> trFnPtrType(const FunctionProtoType *proto, SourceRange range,
                           Rc<ir::SourceInfo> loc,
                           AnonNameGen *liftStructs = nullptr) {
    auto args = Vec<Rc<ir::Type>>::new_();
    for (auto param : proto->getParamTypes()) {
      args.push(trQualType(param, range, liftStructs));
    }
    auto ret = trQualType(proto->getReturnType(), range, liftStructs);
    return mk_type_fnptr(std::move(loc), std::move(args), std::move(ret));
  }

  Rc<ir::Type> trQualType(QualType t, SourceRange range,
                          AnonNameGen *liftStructs = nullptr) {
    t = t.IgnoreParens();
    auto loc = getRange(range);

    if (t.getAsString() == "size_t") {
      return mk_sizet(std::move(loc));
    } else if (auto tydef = dyn_cast<TypedefType>(t)) {
      auto id = ctx.mk_ident(toStr(tydef->getDecl()->getName()), loc.clone());
      return mk_type_typedef(std::move(loc), std::move(id));
#if LLVM_VERSION_MAJOR < 22
    } else if (auto elab = dyn_cast<ElaboratedType>(t)) {
      return trQualType(elab->desugar(), range, liftStructs);
#endif
    } else if (auto ptr = dyn_cast<PointerType>(t)) {
      // Pointer to a (prototyped) function: `R (*)(A0, A1, ...)`. Modeled as a
      // dedicated function-pointer IR type with the argument types collected in
      // order and tupled on emission.
      if (auto proto = ptr->getPointeeType()->getAs<FunctionProtoType>()) {
        return trFnPtrType(proto, range, loc.clone(), liftStructs);
      }
      return mk_pointer_unknown(
          std::move(loc),
          trQualType(ptr->getPointeeType(), /*TODO*/ range, liftStructs));
    } else if (auto proto = t->getAs<FunctionProtoType>()) {
      // A bare (undecayed) function type reached as a value type — treat the
      // function-to-pointer decay result the same as a function pointer.
      return trFnPtrType(proto, range, std::move(loc), liftStructs);
    } else if (auto adj = dyn_cast<AdjustedType>(t)) {
      return trQualType(adj->getOriginalType(), range, liftStructs);
    } else if (auto cat = dyn_cast<ConstantArrayType>(t)) {
      return mk_fixed_array_type(
          std::move(loc),
          trQualType(cat->getElementType(), /* TODO */ range, liftStructs),
          cat->getSize().getZExtValue());
    } else if (auto arr = dyn_cast<ArrayType>(t)) {
      // VLA or incomplete array — decays to pointer
      return mk_pointer_array(
          std::move(loc),
          trQualType(arr->getElementType(), /* TODO */ range, liftStructs));
    } else if (auto rec = dyn_cast<RecordType>(t)) {
      auto decl = rec->getDecl();
      auto key = recordKey(decl);
      Rc<ir::Ident> name;
      if (auto it = structNames.find(key); it != structNames.end()) {
        name = ctx.mk_ident(toStr(it->second), loc.clone());
      } else if (decl->getIdentifier()) {
        structNames.emplace(key, decl->getName().str());
        name = ctx.mk_ident(toStr(decl->getName()), loc.clone());
      } else if (liftStructs) {
        auto nameStr = liftStructs->next();
        structNames.emplace(key, nameStr);
        name = ctx.mk_ident(toStr(nameStr), loc.clone());
        trRecordDecl(name.clone(), decl, liftStructs);
      } else {
        reportUnsupported(
            range, loc, "unsupported anonymous struct/union outside of typedef",
            "");
        return mk_type_err(std::move(loc));
      }
      switch (decl->getTagKind()) {
      case TagTypeKind::Struct: {
        return mk_type_struct(std::move(loc), std::move(name));
      }
      case TagTypeKind::Union: {
        return mk_type_union(std::move(loc), std::move(name));
      }
      default: {
        reportUnsupported(range, loc, "unsupported record kind", "");
        return mk_type_err(std::move(loc));
      }
      }
    }
    if (t->isVoidType()) {
      return mk_void_type(std::move(loc));
    }
    if (isBoolType(t)) {
      return mk_bool_type(std::move(loc));
    }
    if (t->isSpecificBuiltinType(BuiltinType::Float)) {
      return mk_float_type(std::move(loc), 32);
    }
    if (t->isSpecificBuiltinType(BuiltinType::Double)) {
      return mk_float_type(std::move(loc), 64);
    }
    if (t->isFloatingType()) {
      reportUnsupported(range, loc, "unsupported floating-point type ",
                        t.getAsString());
      return mk_type_err(std::move(loc));
    }
    if (t->isSignedIntegerType() || t->isUnsignedIntegerType()) {
      bool isSigned = t->isSignedIntegerType();
      unsigned width = astCtx->getIntWidth(t);
      return mk_int_type(std::move(loc), isSigned, width);
    }

    reportUnsupported(range, loc, "unsupported type ", t->getTypeClassName());
    return mk_type_err(std::move(loc));
  }

  Rc<ir::Type> trTypeAttrs(AttrVec const &attrs, Rc<ir::Type> &&ty,
                           QualType declQt = QualType(),
                           SourceRange declRange = SourceRange()) {
    (void)declQt;
    (void)declRange;
    bool sawNullable = false;
    std::optional<Rc<ir::SourceInfo>> nullableLoc;
    for (auto it = attrs.rbegin(); it != attrs.rend(); ++it) {
      if (auto ann = dyn_cast<AnnotateAttr>(*it)) {
        auto loc = getRange(ann->getRange());
        if (auto ref = isUnaryAttrOf(ann, "pal-refine")) {
          ty = mk_type_refine(std::move(loc), std::move(ty),
                              std::move(ref.value()));
        } else if (auto ref = isUnaryAttrOf(ann, "pal-refine-always")) {
          ty = mk_type_refine_always(std::move(loc), std::move(ty),
                                     std::move(ref.value()));
        } else if (auto ref = isUnaryAttrOf(ann, "pal-refines")) {
          // `_refines(p)` on a flexible array member: an always-true length
          // refinement (relating the FAM length to a sibling field). Modeled
          // as `RefineAlways`; emit lifts the relation into a `pure` fact in
          // the struct predicate.
          ty = mk_type_refine_always(std::move(loc), std::move(ty),
                                     std::move(ref.value()));
        } else if (auto ref = isUnaryAttrOf(ann, "pal-refine-uninit")) {
          ty = mk_type_refine_uninit(std::move(loc), std::move(ty),
                                     std::move(ref.value()));
        } else if (ann->getAnnotation() == "pal-refine-value" &&
                   ann->args_size() == 2) {
          std::optional<unsigned> binding_ctr, pred_ctr;
          if (auto v0 = ann->args_begin()[0]->getIntegerConstantExpr(*astCtx)) {
            binding_ctr = v0->getZExtValue();
          }
          if (auto v1 = ann->args_begin()[1]->getIntegerConstantExpr(*astCtx)) {
            pred_ctr = v1->getZExtValue();
          }
          if (binding_ctr && pred_ctr) {
            ty = mk_type_refine_value(std::move(loc), std::move(ty),
                                      *binding_ctr, *pred_ctr, snippets);
          }
        } else if (ann->getAnnotation() == "pal-plain" &&
                   ann->args_size() == 0) {
          ty = mk_type_plain(std::move(loc), std::move(ty));
        } else if (ann->getAnnotation() == "pal-nullable" &&
                   ann->args_size() == 0) {
          sawNullable = true;
          if (!nullableLoc)
            nullableLoc = getRange(ann->getRange());
          ty = mk_type_nullable(std::move(loc), std::move(ty));
        } else if (ann->getAnnotation() == "pal-array" &&
                   ann->args_size() == 0) {
          ty = mk_type_array(std::move(loc), std::move(ty));
        } else if (ann->getAnnotation() == "pal-arrayptr" &&
                   ann->args_size() == 0) {
          ty = mk_type_arrayptr(std::move(loc), std::move(ty));
        } else if (ann->getAnnotation() == "pal-core-ref" &&
                   ann->args_size() == 0) {
          ty = mk_type_core_ref(std::move(loc), std::move(ty));
        }
      }
    }
    (void)sawNullable;
    (void)nullableLoc;
    return ty;
  }

  bool hasConsumesAttr(AttrVec const &attrs) {
    for (auto it = attrs.rbegin(); it != attrs.rend(); ++it) {
      if (auto ann = dyn_cast<AnnotateAttr>(*it)) {
        if (ann->getAnnotation() == "pal-consumes" && ann->args_size() == 0) {
          return true;
        }
      }
    }
    return false;
  }

  bool hasOutAttr(AttrVec const &attrs) {
    for (auto it = attrs.rbegin(); it != attrs.rend(); ++it) {
      if (auto ann = dyn_cast<AnnotateAttr>(*it)) {
        if (ann->getAnnotation() == "pal-out" && ann->args_size() == 0) {
          return true;
        }
      }
    }
    return false;
  }

  bool isBoolType(QualType t) {
    return t->isUnsignedIntegerType() && astCtx->getIntWidth(t) == 1;
  }

  Rc<ir::Expr> trLValue(Expr *e) {
    auto loc = getRange(e->getSourceRange());

    if (auto generic = dyn_cast<GenericSelectionExpr>(e)) {
      return trLValue(generic->getResultExpr());
    } else if (auto dre = dyn_cast<DeclRefExpr>(e)) {
      auto id = ctx.mk_ident(toStr(dre->getDecl()->getName()), loc.clone());
      return mk_lvalue_var(std::move(loc), std::move(id));
    } else if (auto p = dyn_cast<ParenExpr>(e)) {
      return trLValue(p->getSubExpr());
    } else if (auto uo = dyn_cast<UnaryOperator>(e)) {
      switch (uo->getOpcode()) {
      case UO_Deref:
        return mk_deref(std::move(loc), trRValue(uo->getSubExpr()));

      default:;
        // continue to error case
      }
    } else if (auto m = dyn_cast<MemberExpr>(e)) {
      auto *md = m->getMemberDecl();
      std::string nameStr;
      if (auto *fd = dyn_cast<FieldDecl>(md))
        nameStr = fieldNameStr(fd);
      else
        nameStr = md->getName().str();
      auto id = ctx.mk_ident(toStr(nameStr), loc.clone());
      auto base = m->isArrow() ? mk_deref(loc.clone(), trRValue(m->getBase()))
                               : trLValue(m->getBase());
      return mk_lvalue_member(std::move(loc), std::move(base), std::move(id));
    } else if (auto sub = dyn_cast<ArraySubscriptExpr>(e)) {
      return mk_index(std::move(loc), trRValue(sub->getBase()),
                      trRValue(sub->getIdx()));
    } else if (auto ic = dyn_cast<ImplicitCastExpr>(e)) {
      if (ic->getCastKind() == CK_NoOp) {
        return trLValue(ic->getSubExpr());
      }
    }

    reportUnsupported(e->getSourceRange(), loc,
                      "unsupported lvalue expression ", e->getStmtClassName());
    return mk_lvalue_err(std::move(loc),
                         trQualType(e->getType(), e->getSourceRange()));
  }

  Rc<ir::Expr> trInitList(InitListExpr *init, SourceRange range,
                          Rc<ir::SourceInfo> loc) {
    auto qt = init->getType().getDesugaredType(*astCtx);
    // Handle array initializer lists
    if (auto *cat = dyn_cast<ConstantArrayType>(qt.getTypePtr())) {
      auto elemTy = trQualType(cat->getElementType(), range);
      auto elems = Vec<Rc<ir::Expr>>::new_();
      for (unsigned i = 0; i < init->getNumInits(); ++i) {
        elems.push(trRValue(init->getInit(i)));
      }
      return mk_array_init(std::move(loc), std::move(elemTy), std::move(elems),
                           false);
    }
    auto *rec = dyn_cast<RecordType>(qt.getTypePtr());
    if (!rec) {
      reportUnsupported(range, loc,
                        "unsupported initializer list for non-record type", "");
      return mk_rvalue_err(std::move(loc), trQualType(init->getType(), range));
    }
    auto *decl = rec->getDecl();
    auto it = structNames.find(recordKey(decl));
    if (it == structNames.end()) {
      reportUnsupported(range, loc, "unknown record in initializer list", "");
      return mk_rvalue_err(std::move(loc), trQualType(init->getType(), range));
    }

    if (decl->getTagKind() == TagTypeKind::Union) {
      if (init->getNumInits() != 1) {
        reportUnsupported(range, loc,
                          "union initializer must have exactly one field", "");
        return mk_rvalue_err(std::move(loc),
                             trQualType(init->getType(), range));
      }
      auto unionName = ctx.mk_ident(toStr(it->second), loc.clone());
      auto *fieldInit = init->getInit(0);
      auto *field = init->getInitializedFieldInUnion();
      auto floc = getRange(fieldInit->getSourceRange());
      auto fieldName =
          ctx.mk_ident(toStr(fieldNameStr(field)), std::move(floc));
      return mk_union_init(std::move(loc), std::move(unionName),
                           std::move(fieldName), trRValue(fieldInit));
    }

    if (decl->getTagKind() != TagTypeKind::Struct) {
      reportUnsupported(range, loc,
                        "unsupported initializer list for non-struct type", "");
      return mk_rvalue_err(std::move(loc), trQualType(init->getType(), range));
    }
    auto structName = ctx.mk_ident(toStr(it->second), loc.clone());
    auto builder = StructInitBuilder::new_(loc.clone(), std::move(structName));
    for (unsigned i = 0; i < init->getNumInits(); ++i) {
      auto *fieldInit = init->getInit(i);
      auto *field = *std::next(decl->field_begin(), i);
      // A flexible array member cannot be initialized in a C compound literal;
      // Clang supplies an implicit (empty) initializer for it. Skip it here so
      // the emitter fills it with its default (a length-0 array).
      if (field->getType()->isIncompleteArrayType())
        continue;
      auto floc = getRange(fieldInit->getSourceRange());
      auto fieldName =
          ctx.mk_ident(toStr(fieldNameStr(field)), std::move(floc));
      builder.field(std::move(fieldName), trRValue(fieldInit));
    }
    return builder.build();
  }

  // For a flexible-array-member allocation's trailing size term, return the
  // count operand `n` of `n * sizeof(elem)` or `sizeof(elem) * n` (the
  // non-sizeof multiplicand). Returns nullptr if the term is not a recognized
  // product with a type-sizeof factor.
  static Expr *flexArrayCountSide(Expr *e) {
    auto *mul = dyn_cast<BinaryOperator>(e->IgnoreParenImpCasts());
    if (!mul || mul->getOpcode() != BO_Mul)
      return nullptr;
    auto isTypeSizeof = [](Expr *x) {
      auto *s = dyn_cast<UnaryExprOrTypeTraitExpr>(x->IgnoreParenImpCasts());
      return s && s->getKind() == UETT_SizeOf && s->isArgumentType();
    };
    if (isTypeSizeof(mul->getLHS()))
      return mul->getRHS();
    if (isTypeSizeof(mul->getRHS()))
      return mul->getLHS();
    return nullptr;
  }

  Rc<ir::Expr> trRValue(Expr *e) {
    auto loc = getRange(e->getSourceRange());

    if (auto generic = dyn_cast<GenericSelectionExpr>(e)) {
      return trRValue(generic->getResultExpr());
    }

    if (auto ic = dyn_cast<CastExpr>(e)) {
      switch (ic->getCastKind()) {
      case CK_LValueToRValue:
        if (dyn_cast<CompoundLiteralExpr>(
                ic->getSubExpr()->IgnoreParenImpCasts())) {
          return trRValue(ic->getSubExpr());
        }
        return mk_rvalue_lvalue(std::move(loc), trLValue(ic->getSubExpr()));

      case CK_NoOp:
        return trRValue(ic->getSubExpr());
      case CK_FunctionToPointerDecay:
        // `add` used as a value decays to a function pointer; translate the
        // underlying function reference directly (the DeclRefExpr arm below
        // produces a FnRef for a FunctionDecl).
        return trRValue(ic->getSubExpr());
      case CK_ArrayToPointerDecay: {
        auto *subExpr = ic->getSubExpr()->IgnoreParenImpCasts();
        if (dyn_cast<StringLiteral>(subExpr) ||
            dyn_cast<CompoundLiteralExpr>(subExpr)) {
          return trRValue(ic->getSubExpr());
        }
        return mk_rvalue_lvalue(std::move(loc), trLValue(ic->getSubExpr()));
      }
      case CK_IntegralCast:
      case CK_IntegralToBoolean:
      case CK_PointerToBoolean:
      case CK_FloatingCast:
      case CK_IntegralToFloating:
      case CK_FloatingToIntegral:
      case CK_FloatingToBoolean:
        return mk_rvalue_cast(std::move(loc), trRValue(ic->getSubExpr()),
                              trQualType(ic->getType(), ic->getSourceRange()));

      default:;
        if (isNull(ic)) {
          return mk_int_lit(std::move(loc), mk_bigint("0"_rs),
                            trQualType(ic->getType(), ic->getSourceRange()));
        }

        // Detect (T*) malloc(sizeof(T)) and (T*) malloc(sizeof(T) * n)
        if (auto *call =
                dyn_cast<CallExpr>(ic->getSubExpr()->IgnoreParenImpCasts())) {
          if (auto *callee = call->getDirectCallee()) {
            if (callee->getName() == "malloc" && call->getNumArgs() == 1) {
              auto *arg = call->getArg(0)->IgnoreParenImpCasts();
              // Single element: malloc(sizeof(T))
              if (auto *sizeofExpr = dyn_cast<UnaryExprOrTypeTraitExpr>(arg)) {
                if (sizeofExpr->getKind() == UETT_SizeOf &&
                    sizeofExpr->isArgumentType()) {
                  auto allocTy = trQualType(sizeofExpr->getArgumentType(),
                                            sizeofExpr->getSourceRange());
                  return mk_malloc(std::move(loc), std::move(allocTy));
                }
              }
              // Flexible array member allocation:
              //   malloc(sizeof(struct foo) + n * sizeof(elem))
              // The trailing-array term is runtime sizing that Pulse models via
              // the inline ghost `array_spec`; translate identically to a plain
              // struct malloc of the header type (dropping the array term).
              if (auto *binOp = dyn_cast<BinaryOperator>(arg)) {
                if (binOp->getOpcode() == BO_Add) {
                  auto structSizeofSide =
                      [&](Expr *e) -> const UnaryExprOrTypeTraitExpr * {
                    auto *s = dyn_cast<UnaryExprOrTypeTraitExpr>(
                        e->IgnoreParenImpCasts());
                    if (s && s->getKind() == UETT_SizeOf &&
                        s->isArgumentType() &&
                        s->getArgumentType()->isRecordType())
                      return s;
                    return nullptr;
                  };
                  const UnaryExprOrTypeTraitExpr *structSide =
                      structSizeofSide(binOp->getLHS());
                  Expr *arrayTerm = binOp->getRHS();
                  if (!structSide) {
                    structSide = structSizeofSide(binOp->getRHS());
                    arrayTerm = binOp->getLHS();
                  }
                  if (structSide) {
                    auto allocTy = trQualType(structSide->getArgumentType(),
                                              structSide->getSourceRange());
                    // Extract `n` from the trailing array term `n *
                    // sizeof(elem)` or `sizeof(elem) * n`, so the flexible tail
                    // is sized `n`.
                    if (Expr *countSide = flexArrayCountSide(arrayTerm)) {
                      auto countExpr = trRValue(countSide);
                      return mk_malloc_flex(std::move(loc), std::move(allocTy),
                                            std::move(countExpr));
                    }
                    // Unrecognized array term: fall back to an empty flexible
                    // tail (plain struct malloc).
                    return mk_malloc(std::move(loc), std::move(allocTy));
                  }
                }
              }
              // Array: malloc(sizeof(T) * n) or malloc(n * sizeof(T))
              if (auto *binOp = dyn_cast<BinaryOperator>(arg)) {
                if (binOp->getOpcode() == BO_Mul) {
                  auto *lhs = binOp->getLHS()->IgnoreParenImpCasts();
                  auto *rhs = binOp->getRHS()->IgnoreParenImpCasts();
                  const UnaryExprOrTypeTraitExpr *sizeofSide = nullptr;
                  Expr *countSide = nullptr;
                  if (auto *s = dyn_cast<UnaryExprOrTypeTraitExpr>(lhs)) {
                    if (s->getKind() == UETT_SizeOf && s->isArgumentType()) {
                      sizeofSide = s;
                      countSide = binOp->getRHS();
                    }
                  }
                  if (!sizeofSide) {
                    if (auto *s = dyn_cast<UnaryExprOrTypeTraitExpr>(rhs)) {
                      if (s->getKind() == UETT_SizeOf && s->isArgumentType()) {
                        sizeofSide = s;
                        countSide = binOp->getLHS();
                      }
                    }
                  }
                  if (sizeofSide && countSide) {
                    auto allocTy = trQualType(sizeofSide->getArgumentType(),
                                              sizeofSide->getSourceRange());
                    auto countExpr = trRValue(countSide);
                    return mk_malloc_array(std::move(loc), std::move(allocTy),
                                           std::move(countExpr));
                  }
                }
              }
            }
            // Detect calloc(n, sizeof(T)) and calloc(1, n * sizeof(T))
            if (callee->getName() == "calloc" && call->getNumArgs() == 2) {
              auto *countArg = call->getArg(0)->IgnoreParenImpCasts();
              auto *sizeArg = call->getArg(1)->IgnoreParenImpCasts();
              if (auto *sizeofExpr =
                      dyn_cast<UnaryExprOrTypeTraitExpr>(sizeArg)) {
                if (sizeofExpr->getKind() == UETT_SizeOf &&
                    sizeofExpr->isArgumentType()) {
                  auto allocTy = trQualType(sizeofExpr->getArgumentType(),
                                            sizeofExpr->getSourceRange());
                  // calloc(1, sizeof(T)) → single ref
                  if (auto *intLit = dyn_cast<IntegerLiteral>(countArg)) {
                    if (intLit->getValue() == 1) {
                      return mk_calloc(std::move(loc), std::move(allocTy));
                    }
                  }
                  // calloc(n, sizeof(T)) → array
                  auto countExpr = trRValue(countArg);
                  return mk_calloc_array(std::move(loc), std::move(allocTy),
                                         std::move(countExpr));
                }
              }
              // Flexible array member allocation:
              //   calloc(1, sizeof(struct foo) + n * sizeof(elem))
              // Zeroing counterpart of the malloc FAM idiom above (mirrors
              // MsQuic's `QuicCidNewNullSource`, which allocates the sized
              // block and zeroes it). Translate to a single zeroed struct
              // allocation of the header type, dropping the runtime array term;
              // the zeroed struct's flexible array starts empty (length 0).
              if (auto *intLit = dyn_cast<IntegerLiteral>(countArg)) {
                if (intLit->getValue() == 1) {
                  if (auto *binOp = dyn_cast<BinaryOperator>(sizeArg)) {
                    if (binOp->getOpcode() == BO_Add) {
                      auto structSizeofSide =
                          [&](Expr *e) -> const UnaryExprOrTypeTraitExpr * {
                        auto *s = dyn_cast<UnaryExprOrTypeTraitExpr>(
                            e->IgnoreParenImpCasts());
                        if (s && s->getKind() == UETT_SizeOf &&
                            s->isArgumentType() &&
                            s->getArgumentType()->isRecordType())
                          return s;
                        return nullptr;
                      };
                      const UnaryExprOrTypeTraitExpr *structSide =
                          structSizeofSide(binOp->getLHS());
                      Expr *arrayTerm = binOp->getRHS();
                      if (!structSide) {
                        structSide = structSizeofSide(binOp->getRHS());
                        arrayTerm = binOp->getLHS();
                      }
                      if (structSide) {
                        auto allocTy = trQualType(structSide->getArgumentType(),
                                                  structSide->getSourceRange());
                        // Extract `n` from the trailing array term so the
                        // zeroed flexible tail is sized `n`.
                        if (Expr *countSide = flexArrayCountSide(arrayTerm)) {
                          auto countExpr = trRValue(countSide);
                          return mk_calloc_flex(std::move(loc),
                                                std::move(allocTy),
                                                std::move(countExpr));
                        }
                        // Unrecognized array term: fall back to an empty
                        // flexible tail (plain zeroed struct calloc).
                        return mk_calloc(std::move(loc), std::move(allocTy));
                      }
                    }
                  }
                }
              }
              // calloc(1, n * sizeof(T)) or calloc(1, sizeof(T) * n) → array
              // (e.g. CXPLAT_ALLOC_NONPAGED(n * sizeof(T), ...) → calloc(1,
              // ...))
              if (auto *intLit = dyn_cast<IntegerLiteral>(countArg)) {
                if (intLit->getValue() == 1) {
                  if (auto *binOp = dyn_cast<BinaryOperator>(sizeArg)) {
                    if (binOp->getOpcode() == BO_Mul) {
                      auto *lhs = binOp->getLHS()->IgnoreParenImpCasts();
                      auto *rhs = binOp->getRHS()->IgnoreParenImpCasts();
                      const UnaryExprOrTypeTraitExpr *sizeofSide = nullptr;
                      Expr *countSide = nullptr;
                      if (auto *s = dyn_cast<UnaryExprOrTypeTraitExpr>(lhs)) {
                        if (s->getKind() == UETT_SizeOf &&
                            s->isArgumentType()) {
                          sizeofSide = s;
                          countSide = binOp->getRHS();
                        }
                      }
                      if (!sizeofSide) {
                        if (auto *s = dyn_cast<UnaryExprOrTypeTraitExpr>(rhs)) {
                          if (s->getKind() == UETT_SizeOf &&
                              s->isArgumentType()) {
                            sizeofSide = s;
                            countSide = binOp->getLHS();
                          }
                        }
                      }
                      if (sizeofSide && countSide) {
                        auto allocTy = trQualType(sizeofSide->getArgumentType(),
                                                  sizeofSide->getSourceRange());
                        auto countExpr = trRValue(countSide);
                        return mk_calloc_array(std::move(loc),
                                               std::move(allocTy),
                                               std::move(countExpr));
                      }
                    }
                  }
                }
              }
            }
          }
        }

        // Detect the standard `container_of` idiom, i.e.
        //   (T *)((char *)ptr - offsetof(T, field))
        // as produced by the `_container_of` macro, Linux's `container_of`,
        // MsQuic's `CXPLAT_CONTAINING_RECORD`, etc. The outer `(T *)` cast is a
        // CK_BitCast off a char-pointer subtraction whose right operand is an
        // `OffsetOfExpr` with a single field component. Recover the field
        // pointer, enclosing struct, and field name and build a container
        // projection node. Matching the idiom directly means user code needs no
        // PAL-specific spelling of `container_of`.
        if (ic->getCastKind() == CK_BitCast) {
          if (auto *sub = dyn_cast<BinaryOperator>(
                  ic->getSubExpr()->IgnoreParenImpCasts());
              sub && sub->getOpcode() == BO_Sub) {
            if (auto *ooe = dyn_cast<OffsetOfExpr>(
                    sub->getRHS()->IgnoreParenImpCasts());
                ooe && ooe->getNumComponents() == 1 &&
                ooe->getComponent(0).getKind() == OffsetOfNode::Field) {
              if (auto *field = ooe->getComponent(0).getField()) {
                auto *recordDecl = field->getParent();
                auto structTy = trQualType(astCtx->getRecordType(recordDecl),
                                           ooe->getSourceRange());
                auto fieldId = ctx.mk_ident(toStr(fieldNameStr(field)),
                                            getRange(ooe->getSourceRange()));
                // Strip the `(char *)` cast off the left operand to recover the
                // original field pointer rvalue.
                auto *ptrExpr = sub->getLHS()->IgnoreParenImpCasts();
                if (auto *ptrCast = dyn_cast<CastExpr>(ptrExpr)) {
                  ptrExpr = ptrCast->getSubExpr();
                }
                return mk_container_of(std::move(loc), trRValue(ptrExpr),
                                       std::move(structTy), std::move(fieldId));
              }
            }
          }
        }

        // Detect a cast between a struct pointer and a pointer to one of its
        // transitively-initial members, in either direction. C guarantees a
        // struct pointer round-trips with a pointer to its initial member
        // (C17 6.7.2.1p17): "A pointer to a structure object, suitably
        // converted, points to its initial member ... and vice versa. There
        // may be unnamed padding within a structure object, but not at its
        // beginning." Applying this recursively, a struct pointer is
        // interconvertible with a pointer to the first field of the first
        // field of ... its first field, arbitrarily deep. We recover this
        // chain of initial members and lower a `field -> struct` cast to a
        // nest of per-field container projections (the node `_container_of`
        // produces) and a `struct -> field` cast to a nest of member accesses
        // `&base->f0.f1...`. Both reuse machinery PAL already emits, so
        // nothing downstream changes. A chain of length one reproduces the
        // single-hop first-field cast exactly.
        if (ic->getCastKind() == CK_BitCast) {
          QualType dstTy = ic->getType();
          QualType srcTy = ic->getSubExpr()->getType();
          if (dstTy->isPointerType() && srcTy->isPointerType()) {
            QualType dstPointee = dstTy->getPointeeType();
            QualType srcPointee = srcTy->getPointeeType();

            auto sameType = [&](QualType a, QualType b) {
              return astCtx->hasSameUnqualifiedType(a, b);
            };
            // The non-bitfield first field of a struct pointee, or null.
            auto firstField = [&](QualType pointee) -> FieldDecl * {
              auto *rt = pointee->getAs<RecordType>();
              if (!rt)
                return nullptr;
              auto *rd = rt->getDecl()->getDefinition();
              if (!rd || rd->getTagKind() != TagTypeKind::Struct)
                return nullptr;
              auto it = rd->field_begin();
              if (it == rd->field_end() || it->isBitField())
                return nullptr;
              return *it;
            };
            // The chain of initial members descending from `from` until one
            // has type `target`, e.g. [outer::in, inner::x] for `outer` down
            // to `int`. Empty if `target` is not a transitively-initial member
            // of `from` (a non-struct/bitfield is reached first, or `from`
            // already equals `target`). Depth-capped as a safety net against
            // pathological (e.g. recursive) type graphs.
            auto firstFieldChain =
                [&](QualType from,
                    QualType target) -> std::vector<FieldDecl *> {
              std::vector<FieldDecl *> chain;
              QualType cur = from;
              for (int depth = 0; depth < 32; ++depth) {
                if (sameType(cur, target))
                  return chain;
                FieldDecl *f = firstField(cur);
                if (!f)
                  return {};
                chain.push_back(f);
                if (sameType(f->getType(), target))
                  return chain;
                cur = f->getType();
              }
              return {};
            };

            // (struct S *)p  where p : F *, F transitively-initial member of S.
            auto revChain = firstFieldChain(dstPointee, srcPointee);
            // (F *)s  where s : struct S *, F transitively-initial member of S.
            auto fwdChain = firstFieldChain(srcPointee, dstPointee);

            // At most one direction can match: both would require a cycle in
            // the by-value initial-member graph, impossible as sizes strictly
            // decrease. The `.empty()` guards are defensive.
            if (!revChain.empty() && fwdChain.empty()) {
              // Nest container projections innermost-first: the deepest field
              // (whose parent owns `p`) is applied first.
              auto expr = trRValue(ic->getSubExpr());
              for (auto it = revChain.rbegin(); it != revChain.rend(); ++it) {
                FieldDecl *f = *it;
                auto structTy =
                    trQualType(astCtx->getRecordType(f->getParent()),
                               ic->getSourceRange());
                auto fieldId = ctx.mk_ident(toStr(fieldNameStr(f)),
                                            getRange(ic->getSourceRange()));
                expr = mk_container_of(loc.clone(), std::move(expr),
                                       std::move(structTy), std::move(fieldId));
              }
              return expr;
            }

            if (!fwdChain.empty() && revChain.empty()) {
              // Nest member accesses outermost-first: &(*s).f0.f1...
              auto base = mk_deref(loc.clone(), trRValue(ic->getSubExpr()));
              for (FieldDecl *f : fwdChain) {
                auto fieldId = ctx.mk_ident(toStr(fieldNameStr(f)),
                                            getRange(ic->getSourceRange()));
                base = mk_lvalue_member(loc.clone(), std::move(base),
                                        std::move(fieldId));
              }
              return mk_rvalue_ref(std::move(loc), std::move(base));
            }
          }
        }

        // BitCast (e.g., T* → void*): pass through after malloc/calloc
        // detection. F* functions like memcpy are type-polymorphic.
        if (ic->getCastKind() == CK_BitCast) {
          return trRValue(ic->getSubExpr());
        }

        // continue to error case
      }
    } else if (auto p = dyn_cast<ParenExpr>(e)) {
      return trRValue(p->getSubExpr());
    } else if (auto il = dyn_cast<IntegerLiteral>(e)) {
      if (isBoolType(il->getType())) {
        return mk_bool_lit(std::move(loc), !il->getValue().isZero());
      } else {
        auto ty = trQualType(il->getType(), il->getSourceRange());
        return mk_int_lit(std::move(loc), toBigInt(il->getValue()),
                          std::move(ty));
      }
    } else if (auto fl = dyn_cast<FloatingLiteral>(e)) {
      SmallString<32> value;
      fl->getValue().toString(value);
      auto ty = trQualType(fl->getType(), fl->getSourceRange());
      return mk_float_lit(std::move(loc),
                          ctx.intern_str(toStr(StringRef(value))),
                          std::move(ty));
    } else if (auto cl = dyn_cast<CharacterLiteral>(e)) {
      auto ty = trQualType(cl->getType(), cl->getSourceRange());
      return mk_int_lit(std::move(loc),
                        mk_bigint(toStr(std::to_string(cl->getValue()))),
                        std::move(ty));
    } else if (auto sl = dyn_cast<StringLiteral>(e)) {
      if (sl->getKind() != StringLiteralKind::Ordinary ||
          sl->getCharByteWidth() != 1) {
        reportUnsupported(e->getSourceRange(), loc,
                          "unsupported non-narrow string literal", "");
        return mk_rvalue_err(std::move(loc),
                             trQualType(e->getType(), e->getSourceRange()));
      }
      auto charIsSigned = astCtx->getLangOpts().CharIsSigned;
      auto charWidth = astCtx->getTargetInfo().getCharWidth();
      auto mkCharTy = [&]() {
        return mk_int_type(loc.clone(), charIsSigned, charWidth);
      };
      auto mkCharLit = [&](unsigned char ch) {
        long long value = ch;
        if (charIsSigned && charWidth > 0 &&
            value >= (1LL << (charWidth - 1))) {
          value -= 1LL << charWidth;
        }
        return mk_int_lit(loc.clone(), mk_bigint(toStr(std::to_string(value))),
                          mkCharTy());
      };
      auto elems = Vec<Rc<ir::Expr>>::new_();
      for (unsigned char ch : sl->getBytes()) {
        elems.push(mkCharLit(ch));
      }
      elems.push(mkCharLit(0));
      auto elemTy = mkCharTy();
      return mk_array_init(std::move(loc), std::move(elemTy), std::move(elems),
                           true);
    } else if (auto uo = dyn_cast<UnaryOperator>(e)) {
      switch (uo->getOpcode()) {
      case UO_AddrOf:
        // `&func` where `func` is a function: produce a function reference
        // rather than address-of an lvalue. `&func` and bare `func` (decay)
        // both denote the same function-pointer value.
        if (auto *dre = dyn_cast<DeclRefExpr>(
                uo->getSubExpr()->IgnoreParenImpCasts())) {
          if (auto *fd = dyn_cast<FunctionDecl>(dre->getDecl())) {
            auto id = ctx.mk_ident(toStr(fd->getName()), loc.clone());
            return mk_rvalue_fnref(std::move(loc), std::move(id));
          }
        }
        return mk_rvalue_ref(std::move(loc), trLValue(uo->getSubExpr()));

      case UO_LNot:
        return mk_rvalue_unop(std::move(loc), ir::UnOp::Not(),
                              trRValue(uo->getSubExpr()));

      case UO_Not:
        return mk_rvalue_unop(std::move(loc), ir::UnOp::BitNot(),
                              trRValue(uo->getSubExpr()));

      case UO_Minus:
        return mk_rvalue_unop(std::move(loc), ir::UnOp::Neg(),
                              trRValue(uo->getSubExpr()));

      case UO_PreInc:
        return mk_pre_incr(std::move(loc), trLValue(uo->getSubExpr()));
      case UO_PostInc:
        return mk_post_incr(std::move(loc), trLValue(uo->getSubExpr()));
      case UO_PreDec:
        return mk_pre_decr(std::move(loc), trLValue(uo->getSubExpr()));
      case UO_PostDec:
        return mk_post_decr(std::move(loc), trLValue(uo->getSubExpr()));

      default:;
        // continue to error case
      }
    } else if (auto *bo = dyn_cast<BinaryOperator>(e)) {
      auto m = [&](ir::BinOp op) {
        return mk_rvalue_binop(std::move(loc), std::move(op),
                               trRValue(bo->getLHS()), trRValue(bo->getRHS()));
      };
      switch (bo->getOpcode()) {
      case clang::BO_Add:
        return m(ir::BinOp::Add());
      case clang::BO_Sub:
        return m(ir::BinOp::Sub());
      case clang::BO_Mul:
        return m(ir::BinOp::Mul());
      case clang::BO_Div:
        return m(ir::BinOp::Div());
      case clang::BO_Rem:
        return m(ir::BinOp::Mod());
      case clang::BO_LAnd:
        return m(ir::BinOp::LogAnd());
      case clang::BO_EQ:
        return m(ir::BinOp::Eq());
      case clang::BO_NE: {
        auto loc2 = loc.clone();
        return mk_rvalue_unop(std::move(loc2), ir::UnOp::Not(),
                              m(ir::BinOp::Eq()));
      }
      case clang::BO_LE:
        return m(ir::BinOp::LEq());
      case clang::BO_LT:
        return m(ir::BinOp::Lt());
      case clang::BO_GT:
        return mk_rvalue_binop(std::move(loc), ir::BinOp::Lt(),
                               trRValue(bo->getRHS()), trRValue(bo->getLHS()));
      case clang::BO_GE:
        return mk_rvalue_binop(std::move(loc), ir::BinOp::LEq(),
                               trRValue(bo->getRHS()), trRValue(bo->getLHS()));
      case clang::BO_LOr:
        return m(ir::BinOp::LogOr());
      case clang::BO_And:
        return m(ir::BinOp::BitAnd());
      case clang::BO_Or:
        return m(ir::BinOp::BitOr());
      case clang::BO_Xor:
        return m(ir::BinOp::BitXor());
      case clang::BO_Shl:
        return m(ir::BinOp::Shl());
      case clang::BO_Shr:
        return m(ir::BinOp::Shr());

      case clang::BO_Assign:
        return mk_assign_expr(std::move(loc), trLValue(bo->getLHS()),
                              trRValue(bo->getRHS()));

      case clang::BO_AddAssign:
      case clang::BO_SubAssign:
      case clang::BO_MulAssign:
      case clang::BO_DivAssign:
      case clang::BO_RemAssign:
      case clang::BO_ShlAssign:
      case clang::BO_ShrAssign:
      case clang::BO_AndAssign:
      case clang::BO_OrAssign:
      case clang::BO_XorAssign: {
        auto getBinOp = [](BinaryOperatorKind ok) -> ir::BinOp {
          switch (ok) {
          case BO_AddAssign:
            return ir::BinOp::Add();
          case BO_SubAssign:
            return ir::BinOp::Sub();
          case BO_MulAssign:
            return ir::BinOp::Mul();
          case BO_DivAssign:
            return ir::BinOp::Div();
          case BO_RemAssign:
            return ir::BinOp::Mod();
          case BO_ShlAssign:
            return ir::BinOp::Shl();
          case BO_ShrAssign:
            return ir::BinOp::Shr();
          case BO_AndAssign:
            return ir::BinOp::BitAnd();
          case BO_OrAssign:
            return ir::BinOp::BitOr();
          case BO_XorAssign:
            return ir::BinOp::BitXor();
          default:
            __builtin_unreachable();
          }
        };
        auto op = getBinOp(bo->getOpcode());
        auto lhsRval = mk_rvalue_lvalue(loc.clone(), trLValue(bo->getLHS()));
        auto rhs = trRValue(bo->getRHS());
        auto result = mk_rvalue_binop(loc.clone(), std::move(op),
                                      std::move(lhsRval), std::move(rhs));
        return mk_assign_expr(std::move(loc), trLValue(bo->getLHS()),
                              std::move(result));
      }

      default:;
        // continue to error case
      }
    } else if (auto *c = dyn_cast<CallExpr>(e)) {
      if (auto fd = c->getDirectCallee()) {
        // Detect free(ptr)
        if (fd->getName() == "free" && c->getNumArgs() == 1) {
          auto arg = c->getArg(0);
          // Strip implicit void* cast
          if (auto *ic = dyn_cast<ImplicitCastExpr>(arg)) {
            if (ic->getCastKind() == CK_BitCast) {
              arg = ic->getSubExpr();
            }
          }
          return mk_free(std::move(loc), trRValue(arg));
        }
        // Detect memset(ptr, 0, ...). Only a zero fill value is supported:
        // C `memset` writes raw bytes, and the only fill we can faithfully
        // model for arbitrary types is the all-zero one. Two shapes are
        // recognized:
        //   * memset(ptr, 0, sizeof(T))      — zero a single object of type T
        //     (struct, scalar, ...), emitted as a whole-object write of
        //     `zero_default`.
        //   * memset(ptr, 0, sizeof(T) * n)  — zero an array of byte-sized
        //     element type (e.g. uint8_t, char).
        // Non-zero fill values are rejected with a clear diagnostic.
        if (fd->getName() == "memset" && c->getNumArgs() == 3) {
          auto *ptrArg = c->getArg(0);
          // Strip implicit void* cast
          if (auto *ic = dyn_cast<ImplicitCastExpr>(ptrArg)) {
            if (ic->getCastKind() == CK_BitCast) {
              ptrArg = ic->getSubExpr();
            }
          }
          auto *valArg = c->getArg(1);
          auto *sizeArg = c->getArg(2)->IgnoreParenImpCasts();
          Expr::EvalResult valRes;
          bool valIsZero = valArg->EvaluateAsInt(valRes, *astCtx) &&
                           valRes.Val.isInt() && valRes.Val.getInt() == 0;
          if (!valIsZero) {
            reportUnsupported(e->getSourceRange(), loc,
                              "memset is only supported with a zero fill value",
                              std::string());
            return mk_rvalue_err(std::move(loc),
                                 trQualType(c->getType(), c->getSourceRange()));
          }
          // Zeroing a single object: memset(ptr, 0, sizeof(T)) where the size
          // is a bare sizeof (no multiplication) whose type matches the
          // pointee of `ptr`. Works for any type with a `has_zero_default`
          // instance (structs, scalars, ...): it is emitted as a whole-object
          // write of `zero_default`.
          if (auto *szof = dyn_cast<UnaryExprOrTypeTraitExpr>(sizeArg)) {
            if (szof->getKind() == UETT_SizeOf) {
              auto objQt = szof->getTypeOfArgument();
              auto pointeeQt = ptrArg->getType()->getPointeeType();
              if (!pointeeQt.isNull() &&
                  astCtx->hasSameUnqualifiedType(objQt, pointeeQt)) {
                auto objTy = trQualType(pointeeQt, szof->getSourceRange());
                return mk_memset_zero(std::move(loc), std::move(objTy),
                                      trRValue(ptrArg));
              }
            }
          }
          if (auto *binOp = dyn_cast<BinaryOperator>(sizeArg)) {
            if (binOp->getOpcode() == BO_Mul) {
              auto *lhs = binOp->getLHS()->IgnoreParenImpCasts();
              auto *rhs = binOp->getRHS()->IgnoreParenImpCasts();
              const UnaryExprOrTypeTraitExpr *sizeofSide = nullptr;
              Expr *countSide = nullptr;
              if (auto *s = dyn_cast<UnaryExprOrTypeTraitExpr>(lhs)) {
                if (s->getKind() == UETT_SizeOf && s->isArgumentType()) {
                  sizeofSide = s;
                  countSide = binOp->getRHS();
                }
              }
              if (!sizeofSide) {
                if (auto *s = dyn_cast<UnaryExprOrTypeTraitExpr>(rhs)) {
                  if (s->getKind() == UETT_SizeOf && s->isArgumentType()) {
                    sizeofSide = s;
                    countSide = binOp->getLHS();
                  }
                }
              }
              if (sizeofSide && countSide) {
                auto elemQt = sizeofSide->getArgumentType();
                bool byteSized =
                    !elemQt->isIncompleteType() && !elemQt->isDependentType() &&
                    astCtx->getTypeSizeInChars(elemQt).getQuantity() == 1;
                if (byteSized) {
                  auto elemTy =
                      trQualType(elemQt, sizeofSide->getSourceRange());
                  auto countExpr = trRValue(countSide);
                  return mk_memset(std::move(loc), std::move(elemTy),
                                   trRValue(ptrArg), trRValue(valArg),
                                   std::move(countExpr));
                }
                reportUnsupported(
                    e->getSourceRange(), loc,
                    "memset is only supported on byte-sized element types "
                    "(e.g. uint8_t, char); element type ",
                    elemQt.getAsString());
                return mk_rvalue_err(
                    std::move(loc),
                    trQualType(c->getType(), c->getSourceRange()));
              }
            }
          }
        }
        auto fn = ctx.mk_ident(toStr(fd->getName()),
                               getRange(c->getCallee()->getSourceRange()));
        auto args = Vec<Rc<ir::Expr>>::new_();
        for (auto arg : c->arguments()) {
          args.push(trRValue(arg));
        }
        return mk_rvalue_fncall(std::move(loc), std::move(fn), std::move(args));
      } else {
        // Indirect call through a function-pointer value: `fptr(a, b, ...)`.
        // Clang gives no direct callee; the callee is an rvalue of
        // function-pointer type.
        auto callee = trRValue(c->getCallee());
        auto args = Vec<Rc<ir::Expr>>::new_();
        for (auto arg : c->arguments()) {
          args.push(trRValue(arg));
        }
        return mk_rvalue_fnptr_call(std::move(loc), std::move(callee),
                                    std::move(args));
      }
    } else if (auto *cl = dyn_cast<CompoundLiteralExpr>(e)) {
      auto *init = dyn_cast<InitListExpr>(cl->getInitializer());
      if (!init) {
        reportUnsupported(e->getSourceRange(), loc,
                          "unsupported compound literal without init list", "");
        return mk_rvalue_err(std::move(loc),
                             trQualType(e->getType(), e->getSourceRange()));
      }
      return trInitList(init, e->getSourceRange(), std::move(loc));
    } else if (auto *init = dyn_cast<InitListExpr>(e)) {
      return trInitList(init, e->getSourceRange(), std::move(loc));
    } else if (auto *co = dyn_cast<ConditionalOperator>(e)) {
      return mk_cond(std::move(loc), trRValue(co->getCond()),
                     trRValue(co->getTrueExpr()), trRValue(co->getFalseExpr()));
    } else if (auto *dre = dyn_cast<DeclRefExpr>(e)) {
      if (auto *ecd = dyn_cast<EnumConstantDecl>(dre->getDecl())) {
        const auto val = ecd->getInitVal();
        SmallString<20> valStr;
        val.toString(valStr, 10, val.isSigned());
        return mk_int_lit(std::move(loc), mk_bigint(toStr(StringRef(valStr))),
                          trQualType(e->getType(), e->getSourceRange()));
      }
      // A bare reference to a function (function-to-pointer decay): produce a
      // function reference, identical to `&func`.
      if (auto *fd = dyn_cast<FunctionDecl>(dre->getDecl())) {
        auto id = ctx.mk_ident(toStr(fd->getName()), loc.clone());
        return mk_rvalue_fnref(std::move(loc), std::move(id));
      }
      // Other DeclRefExpr in rvalue context: treat as lvalue read
      return mk_rvalue_lvalue(std::move(loc), trLValue(e));
    } else if (auto *u = dyn_cast<UnaryExprOrTypeTraitExpr>(e)) {
      auto kind = u->getKind();
      if (kind == UETT_SizeOf || kind == UETT_AlignOf ||
          kind == UETT_PreferredAlignOf) {
        auto argTy = u->getTypeOfArgument();
        if (argTy->isIncompleteType() || argTy->isDependentType() ||
            argTy->isVariableArrayType()) {
          reportUnsupported(
              e->getSourceRange(), loc,
              "sizeof/_Alignof on incomplete, dependent, or VLA type ", "");
          return mk_rvalue_err(std::move(loc),
                               trQualType(e->getType(), e->getSourceRange()));
        }
        auto ty = trQualType(argTy, e->getSourceRange());
        if (kind == UETT_SizeOf) {
          return mk_sizeof(std::move(loc), std::move(ty));
        } else {
          return mk_alignof(std::move(loc), std::move(ty));
        }
      }
    }

    reportUnsupported(e->getSourceRange(), loc,
                      "unsupported rvalue expression ", e->getStmtClassName());
    return mk_rvalue_err(std::move(loc),
                         trQualType(e->getType(), e->getSourceRange()));
  }

  bool isNull(Expr *e) {
    if (auto *c = dyn_cast<CastExpr>(e)) {
      if (c->getCastKind() == CK_NullToPointer)
        return true;
      return isNull(c->getSubExpr());
    } else if (auto *p = dyn_cast<ParenExpr>(e)) {
      return isNull(p->getSubExpr());
    } else {
      return false;
    }
  }

  Vec<Rc<ir::Stmt>> trStmts(Stmt *stmt) {
    auto stmts = Vec<Rc<ir::Stmt>>::new_();
    if (stmt)
      trStmt(stmts, stmt);
    return stmts;
  }

  rust::Unit trStmt(Vec<Rc<ir::Stmt>> &stmts, Stmt *stmt) {
    auto loc = getRange(stmt->getSourceRange());

    if (auto *bo = dyn_cast<BinaryOperator>(stmt)) {
      switch (bo->getOpcode()) {
      case clang::BO_Assign:
        return stmts.push(mk_assign(std::move(loc), trLValue(bo->getLHS()),
                                    trRValue(bo->getRHS())));

      case clang::BO_Comma:
        trStmt(stmts, bo->getLHS());
        return trStmt(stmts, bo->getRHS());

      case clang::BO_AddAssign:
      case clang::BO_SubAssign:
      case clang::BO_MulAssign:
      case clang::BO_DivAssign:
      case clang::BO_RemAssign:
      case clang::BO_ShlAssign:
      case clang::BO_ShrAssign:
      case clang::BO_AndAssign:
      case clang::BO_OrAssign:
      case clang::BO_XorAssign: {
        auto getBinOp = [](BinaryOperatorKind ok) -> ir::BinOp {
          switch (ok) {
          case BO_AddAssign:
            return ir::BinOp::Add();
          case BO_SubAssign:
            return ir::BinOp::Sub();
          case BO_MulAssign:
            return ir::BinOp::Mul();
          case BO_DivAssign:
            return ir::BinOp::Div();
          case BO_RemAssign:
            return ir::BinOp::Mod();
          case BO_ShlAssign:
            return ir::BinOp::Shl();
          case BO_ShrAssign:
            return ir::BinOp::Shr();
          case BO_AndAssign:
            return ir::BinOp::BitAnd();
          case BO_OrAssign:
            return ir::BinOp::BitOr();
          case BO_XorAssign:
            return ir::BinOp::BitXor();
          default:
            __builtin_unreachable();
          }
        };
        auto op = getBinOp(bo->getOpcode());
        auto lhsRval = mk_rvalue_lvalue(loc.clone(), trLValue(bo->getLHS()));
        auto rhs = trRValue(bo->getRHS());
        auto result = mk_rvalue_binop(loc.clone(), std::move(op),
                                      std::move(lhsRval), std::move(rhs));
        return stmts.push(mk_assign(std::move(loc), trLValue(bo->getLHS()),
                                    std::move(result)));
      }

      default:;
        // continue to error case
      }
    } else if (auto *uo = dyn_cast<UnaryOperator>(stmt)) {
      auto lhs = trLValue(uo->getSubExpr());
      switch (uo->getOpcode()) {
      case UO_PreInc: {
        auto exprLoc = loc.clone();
        return stmts.push(mk_call(
            std::move(loc), mk_pre_incr(std::move(exprLoc), std::move(lhs))));
      }
      case UO_PostInc: {
        auto exprLoc = loc.clone();
        return stmts.push(mk_call(
            std::move(loc), mk_post_incr(std::move(exprLoc), std::move(lhs))));
      }
      case UO_PreDec: {
        auto exprLoc = loc.clone();
        return stmts.push(mk_call(
            std::move(loc), mk_pre_decr(std::move(exprLoc), std::move(lhs))));
      }
      case UO_PostDec: {
        auto exprLoc = loc.clone();
        return stmts.push(mk_call(
            std::move(loc), mk_post_decr(std::move(exprLoc), std::move(lhs))));
      }
      default:;
        // continue to error case
      }
    } else if (auto *i = dyn_cast<IfStmt>(stmt)) {
      auto thenStmt = i->getThen();
      auto enss = Vec<Rc<ir::Expr>>::new_();
      if (auto attrThen = dyn_cast_or_null<AttributedStmt>(thenStmt)) {
        for (auto attr : attrThen->getAttrs()) {
          if (auto ens = isUnaryAttrOf(attr, "pal-ensures")) {
            enss.push(std::move(ens.value()));
          }
        }
        thenStmt = attrThen->getSubStmt();
      }
      return stmts.push(mk_if(loc.clone(), trRValue(i->getCond()),
                              trStmts(thenStmt), trStmts(i->getElse()),
                              std::move(enss)));
    } else if (auto *w = dyn_cast<WhileStmt>(stmt)) {
      auto body = w->getBody();
      auto invs = Vec<Rc<ir::Expr>>::new_();
      auto reqs = Vec<Rc<ir::Expr>>::new_();
      auto enss = Vec<Rc<ir::Expr>>::new_();
      if (auto attrBody = dyn_cast<AttributedStmt>(body)) {
        for (auto attr : attrBody->getAttrs()) {
          if (auto inv = isUnaryAttrOf(attr, "pal-invariant")) {
            invs.push(std::move(inv.value()));
          } else if (auto req = isUnaryAttrOf(attr, "pal-requires")) {
            reqs.push(std::move(req.value()));
          } else if (auto ens = isUnaryAttrOf(attr, "pal-ensures")) {
            enss.push(std::move(ens.value()));
          }
        }
        body = attrBody->getSubStmt();
      }
      auto savedIncrement = forLoopIncrement;
      forLoopIncrement = nullptr;
      auto bodyStmts = trStmts(body);
      forLoopIncrement = savedIncrement;
      return stmts.push(mk_while(loc.clone(), trRValue(w->getCond()),
                                 std::move(invs), std::move(reqs),
                                 std::move(enss), std::move(bodyStmts)));
    } else if (auto *d = dyn_cast<DoStmt>(stmt)) {
      // Desugar `do { body } while (cond)` into a `while` loop. There are two
      // desugarings, and the presence of a *top-level* `continue` in the body
      // selects between them:
      //
      //   * Clean desugaring (no top-level `continue`):
      //         bool cont = true; bool first = true;
      //         while (cont) { body; first = false; cont = cond; }
      //     Here `cont` (the "continuation" flag) drives the loop: it is forced
      //     true so the body runs at least once (do-while semantics), then the
      //     guard is re-evaluated at the *end* of the body via `cont = cond`.
      //
      //   * Legacy desugaring (a top-level `continue` is present):
      //         bool first = true;
      //         while (first || cond) { first = false; body; }
      //     We cannot use the clean form here: a top-level `continue` would
      //     jump past the trailing `cont = cond` update, so the guard would
      //     never be re-evaluated and the loop could spin forever. The legacy
      //     form keeps the guard `cond` in the `while` condition (re-evaluated
      //     on each iteration, side effects and all) where `continue` cannot
      //     skip it.
      //
      // `hasTopLevelContinue` decides which form to use. It treats a nested
      // for/while/do-while as a boundary (a `continue` inside one binds to that
      // inner loop, not to us) but descends into if/switch/blocks/labels, since
      // a `continue` there does target this do-while.
      //
      // Annotations:
      //   * `_do_while_first(name)` names the first-iteration flag so the user
      //     can mention it in invariants (e.g. `first ==> i < n`).
      //   * `_do_while_cond(name)` names the continuation flag `cont`. This is
      //     needed for impure guards: the auto-linking invariant (below) is
      //     omitted when the guard has side effects, so the user must name
      //     `cont` and supply their own *pure* linking invariant relating it to
      //     program state (e.g. `cont == (s.x < 10)`).

      // Extract annotations and check for _do_while_first / _do_while_cond
      auto body = d->getBody();
      auto invs = Vec<Rc<ir::Expr>>::new_();
      auto reqs = Vec<Rc<ir::Expr>>::new_();
      auto enss = Vec<Rc<ir::Expr>>::new_();
      std::string flagName;
      std::string condName;
      if (auto attrBody = dyn_cast<AttributedStmt>(body)) {
        for (auto attr : attrBody->getAttrs()) {
          if (auto inv = isUnaryAttrOf(attr, "pal-invariant")) {
            invs.push(std::move(inv.value()));
          } else if (auto req = isUnaryAttrOf(attr, "pal-requires")) {
            reqs.push(std::move(req.value()));
          } else if (auto ens = isUnaryAttrOf(attr, "pal-ensures")) {
            enss.push(std::move(ens.value()));
          } else if (auto ann = dyn_cast<AnnotateAttr>(attr)) {
            if (ann->getAnnotation() == "pal-do-while-first" &&
                ann->args_size() == 1) {
              auto *arg = (*ann->args_begin())->IgnoreParenImpCasts();
              if (auto *sl = dyn_cast<StringLiteral>(arg)) {
                flagName = sl->getString().str();
              }
            } else if (ann->getAnnotation() == "pal-do-while-cond" &&
                       ann->args_size() == 1) {
              auto *arg = (*ann->args_begin())->IgnoreParenImpCasts();
              if (auto *sl = dyn_cast<StringLiteral>(arg)) {
                condName = sl->getString().str();
              }
            }
          }
        }
        body = attrBody->getSubStmt();
      }

      // First-iteration flag: named by _do_while_first, else auto-generated.
      // Its
      // `_live` invariant is auto-injected only when the name is auto-generated
      // (a user-named flag is expected to be mentioned in the user's
      // invariant).
      bool firstIsAuto = flagName.empty();
      if (firstIsAuto) {
        static int doCounter = 0;
        flagName = "__do_first_" + std::to_string(doCounter++);
      }
      auto firstId = ctx.mk_ident(toStr(flagName), loc.clone());

      // Continuation flag `cont`: named by _do_while_cond, else auto-generated.
      // As with `first`, `_live(cont)` is auto-injected only when the name is
      // auto-generated; a user-named `cont` is expected to appear (with its own
      // `_live`) in the user's invariants.
      bool condIsAuto = condName.empty();
      if (condIsAuto) {
        static int doContCounter = 0;
        condName = "__do_cont_" + std::to_string(doContCounter++);
      }
      auto contId = ctx.mk_ident(toStr(condName), loc.clone());

      if (!hasTopLevelContinue(body)) {
        // Clean desugaring: no top-level `continue`.

        // bool cont; cont = true;
        stmts.push(mk_var_decl(loc.clone(), contId.clone(),
                               mk_bool_type(loc.clone())));
        stmts.push(mk_assign(loc.clone(),
                             mk_lvalue_var(loc.clone(), contId.clone()),
                             mk_bool_lit(loc.clone(), true)));
        // bool first; first = true;
        stmts.push(mk_var_decl(loc.clone(), firstId.clone(),
                               mk_bool_type(loc.clone())));
        stmts.push(mk_assign(loc.clone(),
                             mk_lvalue_var(loc.clone(), firstId.clone()),
                             mk_bool_lit(loc.clone(), true)));

        // while condition: cont
        auto whileCond = mk_rvalue_lvalue(
            loc.clone(), mk_lvalue_var(loc.clone(), contId.clone()));

        // Inject _live(cont) and _live(first) when the respective flag name was
        // auto-generated (a user-named flag carries its own _live).
        if (condIsAuto) {
          invs.push(
              mk_live(loc.clone(), mk_lvalue_var(loc.clone(), contId.clone())));
        }
        if (firstIsAuto) {
          invs.push(mk_live(loc.clone(),
                            mk_lvalue_var(loc.clone(), firstId.clone())));
        }

        // Link the internal `cont` flag back to the loop condition so the body
        // knows `cond` held on re-entry. The guard `while (cont)` alone conveys
        // nothing to the solver about `cond`, yet many bodies rely on it (e.g.
        // a body doing `i = i + 1` needs `i < n` to maintain `i <= n`). We
        // inject:
        //     cont == (first || cond)
        // which, together with the guard `cont == true`, re-supplies exactly
        // the `first || cond` fact the original do-while guard would have
        // provided.
        //
        // This is only sound when `cond` is a *pure* expression: the invariant
        // is a `with_pure` proposition, so an impure guard (e.g. `while (f())`)
        // cannot appear in it. When the guard has side effects we omit the
        // linking invariant entirely (such loops must instead carry a
        // user-written invariant relating program state to the guard's result).
        if (!d->getCond()->HasSideEffects(*astCtx)) {
          auto firstRead = mk_rvalue_lvalue(
              loc.clone(), mk_lvalue_var(loc.clone(), firstId.clone()));
          auto contReadInv = mk_rvalue_lvalue(
              loc.clone(), mk_lvalue_var(loc.clone(), contId.clone()));
          auto firstOrCond =
              mk_rvalue_binop(loc.clone(), ir::BinOp::LogOr(),
                              std::move(firstRead), trRValue(d->getCond()));
          invs.push(mk_rvalue_binop(loc.clone(), ir::BinOp::Eq(),
                                    std::move(contReadInv),
                                    std::move(firstOrCond)));
        }

        // Build body: original_body; first = false; cont = cond;
        auto bodyStmts = Vec<Rc<ir::Stmt>>::new_();
        auto savedIncrement = forLoopIncrement;
        forLoopIncrement = nullptr;
        trStmt(bodyStmts, body);
        forLoopIncrement = savedIncrement;
        bodyStmts.push(mk_assign(loc.clone(),
                                 mk_lvalue_var(loc.clone(), firstId.clone()),
                                 mk_bool_lit(loc.clone(), false)));
        bodyStmts.push(mk_assign(loc.clone(),
                                 mk_lvalue_var(loc.clone(), contId.clone()),
                                 trRValue(d->getCond())));

        return stmts.push(mk_while(std::move(loc), std::move(whileCond),
                                   std::move(invs), std::move(reqs),
                                   std::move(enss), std::move(bodyStmts)));
      }

      // Legacy desugaring: body has a top-level `continue`.
      //
      // The `cont` flag plays no role here (the guard is `first || cond`), but
      // if the user named it via `_do_while_cond(cont)` we still declare and
      // initialize it. That way an invariant / `_live` referencing `cont`
      // resolves to a real, initialized variable and the generated F* file does
      // not break -- even though nothing in this desugaring reads `cont`.
      if (!condIsAuto) {
        stmts.push(mk_var_decl(loc.clone(), contId.clone(),
                               mk_bool_type(loc.clone())));
        stmts.push(mk_assign(loc.clone(),
                             mk_lvalue_var(loc.clone(), contId.clone()),
                             mk_bool_lit(loc.clone(), true)));
      }

      // bool first; first = true;
      stmts.push(
          mk_var_decl(loc.clone(), firstId.clone(), mk_bool_type(loc.clone())));
      stmts.push(mk_assign(loc.clone(),
                           mk_lvalue_var(loc.clone(), firstId.clone()),
                           mk_bool_lit(loc.clone(), true)));

      // while condition: first || cond
      auto flagRead = mk_rvalue_lvalue(
          loc.clone(), mk_lvalue_var(loc.clone(), firstId.clone()));
      auto whileCond =
          mk_rvalue_binop(loc.clone(), ir::BinOp::LogOr(), std::move(flagRead),
                          trRValue(d->getCond()));

      // Add _live(first) to invariants when the name is auto-generated.
      if (firstIsAuto) {
        invs.push(
            mk_live(loc.clone(), mk_lvalue_var(loc.clone(), firstId.clone())));
      }

      // Build body: first = false; original_body;
      auto bodyStmts = Vec<Rc<ir::Stmt>>::new_();
      bodyStmts.push(mk_assign(loc.clone(),
                               mk_lvalue_var(loc.clone(), firstId.clone()),
                               mk_bool_lit(loc.clone(), false)));
      auto savedIncrement = forLoopIncrement;
      forLoopIncrement = nullptr;
      trStmt(bodyStmts, body);
      forLoopIncrement = savedIncrement;

      return stmts.push(mk_while(std::move(loc), std::move(whileCond),
                                 std::move(invs), std::move(reqs),
                                 std::move(enss), std::move(bodyStmts)));
    } else if (auto *sw = dyn_cast<SwitchStmt>(stmt)) {
      // Desugar: switch (scrutinee) { case v1: s1; case v2: s2; default: sd }
      //      --> let scrut = scrutinee;
      //          bool hit = false; bool brk = false;
      //          if (!brk && (hit || scrut == v1)) { hit = true; s1 }
      //          if (!brk && (hit || scrut == v2)) { hit = true; s2 }
      //          if (!brk) { sd }
      // break inside case bodies sets brk = true.

      // Evaluate scrutinee
      auto scrutRval = trRValue(sw->getCond());
      auto scrutTy =
          trQualType(sw->getCond()->getType(), sw->getCond()->getSourceRange());

      // Bind the scrutinee once as an immutable value.
      static int switchCounter = 0;
      auto switchIndex = switchCounter++;
      auto scrutName = "__switch_scrut_" + std::to_string(switchIndex);
      auto scrutId = ctx.mk_ident(toStr(scrutName), loc.clone());
      stmts.push(mk_let_stmt(loc.clone(), scrutId.clone(), scrutTy.clone(),
                             std::move(scrutRval)));

      // Collect cases from the switch body. A switch postcondition is used as
      // the join invariant for every desugared case test.
      auto *body = sw->getBody();
      std::vector<Rc<ir::Expr>> switchEnss;
      if (auto attrBody = dyn_cast<AttributedStmt>(body)) {
        for (auto attr : attrBody->getAttrs()) {
          if (auto ens = isUnaryAttrOf(attr, "pal-ensures")) {
            switchEnss.push_back(std::move(ens.value()));
          }
        }
        body = attrBody->getSubStmt();
      }
      auto *comp = dyn_cast<CompoundStmt>(body);
      if (!comp) {
        reportUnsupported(body->getSourceRange(), loc,
                          "switch body must be a compound statement", "");
        return {};
      }

      auto containsSwitchBreak = [&](auto &self, Stmt *s) -> bool {
        if (dyn_cast<BreakStmt>(s))
          return true;
        if (dyn_cast<SwitchStmt>(s) || dyn_cast<ForStmt>(s) ||
            dyn_cast<WhileStmt>(s) || dyn_cast<DoStmt>(s))
          return false;
        for (auto *child : s->children()) {
          if (child && self(self, child))
            return true;
        }
        return false;
      };
      bool switchCanBreak = false;
      for (auto *child : comp->body())
        switchCanBreak |= containsSwitchBreak(containsSwitchBreak, child);

      // Walk the compound statement collecting case/default groups
      // Clang attaches only the first statement after a label to CaseStmt or
      // DefaultStmt. The remaining statements are siblings in the compound
      // body, but are still controlled by that label in C.
      struct SwitchGroup {
        Stmt *label;
        bool isDefault;
        std::vector<Expr *> caseValues;
        std::vector<Stmt *> body;
      };
      std::vector<SwitchGroup> groups;
      bool seenDefault = false;
      SwitchGroup *currentGroup = nullptr;
      for (auto *child : comp->body()) {
        if (auto *cs = dyn_cast<CaseStmt>(child)) {
          auto childLoc = getRange(child->getSourceRange());
          if (seenDefault) {
            reportUnsupported(cs->getSourceRange(), childLoc,
                              "default must be the last case in switch", "");
            break;
          }

          groups.push_back({child, false, {}, {}});
          currentGroup = &groups.back();
          Stmt *caseBody = child;
          while (auto *innerCs = dyn_cast<CaseStmt>(caseBody)) {
            currentGroup->caseValues.push_back(innerCs->getLHS());
            caseBody = innerCs->getSubStmt();
          }
          if (caseBody)
            currentGroup->body.push_back(caseBody);
        } else if (auto *ds = dyn_cast<DefaultStmt>(child)) {
          seenDefault = true;
          groups.push_back({child, true, {}, {}});
          currentGroup = &groups.back();
          if (ds->getSubStmt())
            currentGroup->body.push_back(ds->getSubStmt());
        } else if (currentGroup) {
          currentGroup->body.push_back(child);
        } else {
          // Statements before the first label are unreachable in C, but retain
          // the old behavior so malformed inputs still receive diagnostics.
          trStmt(stmts, child);
        }
      }

      // A switch whose cases all end in a direct break has no fall-through.
      // Emit it as one match and omit the terminal breaks.
      bool hasOnlyTerminalBreaks = !groups.empty();
      std::vector<SwitchGroup *> cases;
      SwitchGroup *defaultGroup = nullptr;
      for (auto &group : groups) {
        bool hasTerminalBreak =
            !group.body.empty() && isa<BreakStmt>(group.body.back());
        if (!hasTerminalBreak) {
          hasOnlyTerminalBreaks = false;
          break;
        }

        size_t bodySize = group.body.size() - 1;
        if (group.isDefault) {
          defaultGroup = &group;
        } else {
          cases.push_back(&group);
        }
        for (size_t i = 0; i < bodySize; i++) {
          if (containsSwitchBreak(containsSwitchBreak, group.body[i])) {
            hasOnlyTerminalBreaks = false;
            break;
          }
        }
        if (!hasOnlyTerminalBreaks)
          break;
      }

      if (hasOnlyTerminalBreaks && !cases.empty() && !switchEnss.empty()) {
        auto makeBody = [&](SwitchGroup &group) {
          auto bodyStmts = Vec<Rc<ir::Stmt>>::new_();
          size_t bodySize = group.body.size() - 1;
          for (size_t i = 0; i < bodySize; i++)
            trStmt(bodyStmts, group.body[i]);
          return bodyStmts;
        };

        bool canUseMatch = true;
        for (auto *group : cases) {
          for (auto *caseValue : group->caseValues) {
            Expr::EvalResult result;
            if (!caseValue->EvaluateAsInt(result, *astCtx) ||
                !result.Val.isInt()) {
              canUseMatch = false;
              break;
            }
          }
          if (!canUseMatch)
            break;
        }

        if (canUseMatch) {
          auto matchBranches = Vec<Rc<ir::MatchBranch>>::new_();
          for (auto *group : cases) {
            auto patterns = Vec<Rc<ir::Expr>>::new_();
            for (auto *caseValue : group->caseValues) {
              Expr::EvalResult result;
              bool evaluated = caseValue->EvaluateAsInt(result, *astCtx);
              assert(evaluated && result.Val.isInt());
              patterns.push(mk_int_lit(getRange(caseValue->getSourceRange()),
                                       toBigInt(result.Val.getInt()),
                                       scrutTy.clone()));
            }
            matchBranches.push(
                mk_match_branch(std::move(patterns), makeBody(*group)));
          }

          auto defaultBody = defaultGroup ? makeBody(*defaultGroup)
                                          : Vec<Rc<ir::Stmt>>::new_();
          auto matchEnss = Vec<Rc<ir::Expr>>::new_();
          auto combined = switchEnss.front().clone();
          for (size_t i = 1; i < switchEnss.size(); i++) {
            combined =
                mk_rvalue_binop(loc.clone(), ir::BinOp::LogAnd(),
                                std::move(combined), switchEnss[i].clone());
          }
          matchEnss.push(std::move(combined));
          stmts.push(mk_match(loc.clone(),
                              mk_lvalue_var(loc.clone(), scrutId.clone()),
                              std::move(matchBranches), std::move(defaultBody),
                              std::move(matchEnss)));
          return {};
        }
      }

      // General switches retain explicit hit and break state to model
      // fall-through.
      auto hitName = "__switch_hit_" + std::to_string(switchIndex);
      auto brkName = "__switch_brk_" + std::to_string(switchIndex);
      auto hitId = ctx.mk_ident(toStr(hitName), loc.clone());
      auto brkId = ctx.mk_ident(toStr(brkName), loc.clone());

      stmts.push(
          mk_var_decl(loc.clone(), hitId.clone(), mk_bool_type(loc.clone())));
      stmts.push(mk_assign(loc.clone(),
                           mk_lvalue_var(loc.clone(), hitId.clone()),
                           mk_bool_lit(loc.clone(), false)));
      stmts.push(
          mk_var_decl(loc.clone(), brkId.clone(), mk_bool_type(loc.clone())));
      stmts.push(mk_assign(loc.clone(),
                           mk_lvalue_var(loc.clone(), brkId.clone()),
                           mk_bool_lit(loc.clone(), false)));

      auto savedSwitchBreak = switchBreakId;
      switchBreakId = new Rc<ir::Ident>(brkId.clone());

      auto caseEnss = [&]() {
        auto enss = Vec<Rc<ir::Expr>>::new_();
        if (!switchEnss.empty()) {
          auto combined = switchEnss.front().clone();
          for (size_t i = 1; i < switchEnss.size(); i++) {
            combined =
                mk_rvalue_binop(loc.clone(), ir::BinOp::LogAnd(),
                                std::move(combined), switchEnss[i].clone());
          }
          combined = mk_rvalue_binop(
              loc.clone(), ir::BinOp::LogAnd(), std::move(combined),
              mk_live(loc.clone(), mk_lvalue_var(loc.clone(), hitId.clone())));
          combined = mk_rvalue_binop(
              loc.clone(), ir::BinOp::LogAnd(), std::move(combined),
              mk_live(loc.clone(), mk_lvalue_var(loc.clone(), brkId.clone())));
          enss.push(std::move(combined));
        }
        return enss;
      };

      for (auto &group : groups) {
        auto childLoc = getRange(group.label->getSourceRange());
        if (!group.isDefault) {
          // Build match condition: scrut == v1 || scrut == v2 || ...
          Rc<ir::Expr> matchCond = mk_bool_lit(childLoc.clone(), false);
          for (auto *cv : group.caseValues) {
            auto scrutRead = mk_lvalue_var(childLoc.clone(), scrutId.clone());
            auto caseVal = trRValue(cv->IgnoreParenImpCasts());
            auto eq = mk_rvalue_binop(childLoc.clone(), ir::BinOp::Eq(),
                                      std::move(scrutRead), std::move(caseVal));
            matchCond = mk_rvalue_binop(childLoc.clone(), ir::BinOp::LogOr(),
                                        std::move(matchCond), std::move(eq));
          }

          // Full condition: !brk && (hit || matchCond)
          auto notBrk = mk_rvalue_unop(
              childLoc.clone(), ir::UnOp::Not(),
              mk_rvalue_lvalue(childLoc.clone(),
                               mk_lvalue_var(childLoc.clone(), brkId.clone())));
          auto hitRead = mk_rvalue_lvalue(
              childLoc.clone(), mk_lvalue_var(childLoc.clone(), hitId.clone()));
          auto hitOrMatch =
              mk_rvalue_binop(childLoc.clone(), ir::BinOp::LogOr(),
                              std::move(hitRead), std::move(matchCond));
          auto cond = mk_rvalue_binop(childLoc.clone(), ir::BinOp::LogAnd(),
                                      std::move(notBrk), std::move(hitOrMatch));

          // Body: hit = true; case_stmts
          auto thenStmts = Vec<Rc<ir::Stmt>>::new_();
          thenStmts.push(mk_assign(
              childLoc.clone(), mk_lvalue_var(childLoc.clone(), hitId.clone()),
              mk_bool_lit(childLoc.clone(), true)));
          for (auto *bodyStmt : group.body)
            trStmt(thenStmts, bodyStmt);

          auto elseStmts = Vec<Rc<ir::Stmt>>::new_();
          stmts.push(mk_if(std::move(childLoc), std::move(cond),
                           std::move(thenStmts), std::move(elseStmts),
                           caseEnss()));

        } else {
          if (!switchCanBreak) {
            // With no break belonging to this switch, reaching default means
            // its body runs. Emitting it directly preserves terminating
            // returns without introducing an unnecessary conditional join.
            stmts.push(mk_assign(childLoc.clone(),
                                 mk_lvalue_var(childLoc.clone(), hitId.clone()),
                                 mk_bool_lit(childLoc.clone(), true)));
            for (auto *bodyStmt : group.body)
              trStmt(stmts, bodyStmt);
            continue;
          }
          // Condition: !brk
          auto notBrk = mk_rvalue_unop(
              childLoc.clone(), ir::UnOp::Not(),
              mk_rvalue_lvalue(childLoc.clone(),
                               mk_lvalue_var(childLoc.clone(), brkId.clone())));

          auto thenStmts = Vec<Rc<ir::Stmt>>::new_();
          thenStmts.push(mk_assign(
              childLoc.clone(), mk_lvalue_var(childLoc.clone(), hitId.clone()),
              mk_bool_lit(childLoc.clone(), true)));
          for (auto *bodyStmt : group.body)
            trStmt(thenStmts, bodyStmt);

          auto elseStmts = Vec<Rc<ir::Stmt>>::new_();
          stmts.push(mk_if(std::move(childLoc), std::move(notBrk),
                           std::move(thenStmts), std::move(elseStmts),
                           caseEnss()));
        }
      }

      delete switchBreakId;
      switchBreakId = savedSwitchBreak;
      return {};
    } else if (auto *f = dyn_cast<ForStmt>(stmt)) {
      // Desugar: for (init; cond; incr) body
      //      --> init; while (cond) { body; incr; }
      if (f->getInit())
        trStmt(stmts, f->getInit());

      auto cond = f->getCond() ? trRValue(f->getCond())
                               : mk_bool_lit(loc.clone(), true);

      auto body = f->getBody();
      auto invs = Vec<Rc<ir::Expr>>::new_();
      auto reqs = Vec<Rc<ir::Expr>>::new_();
      auto enss = Vec<Rc<ir::Expr>>::new_();
      if (auto attrBody = dyn_cast<AttributedStmt>(body)) {
        for (auto attr : attrBody->getAttrs()) {
          if (auto inv = isUnaryAttrOf(attr, "pal-invariant")) {
            invs.push(std::move(inv.value()));
          } else if (auto req = isUnaryAttrOf(attr, "pal-requires")) {
            reqs.push(std::move(req.value()));
          } else if (auto ens = isUnaryAttrOf(attr, "pal-ensures")) {
            enss.push(std::move(ens.value()));
          }
        }
        body = attrBody->getSubStmt();
      }

      auto savedIncrement = forLoopIncrement;
      forLoopIncrement = f->getInc();
      auto bodyStmts = trStmts(body);
      if (f->getInc())
        trStmt(bodyStmts, f->getInc());
      forLoopIncrement = savedIncrement;

      return stmts.push(mk_while(loc.clone(), std::move(cond), std::move(invs),
                                 std::move(reqs), std::move(enss),
                                 std::move(bodyStmts)));
    } else if (dyn_cast<BreakStmt>(stmt)) {
      if (switchBreakId) {
        // Inside a switch: set break flag instead of emitting break
        return stmts.push(mk_assign(
            loc.clone(), mk_lvalue_var(loc.clone(), switchBreakId->clone()),
            mk_bool_lit(std::move(loc), true)));
      }
      return stmts.push(mk_break(std::move(loc)));
    } else if (dyn_cast<ContinueStmt>(stmt)) {
      if (forLoopIncrement)
        trStmt(stmts, forLoopIncrement);
      return stmts.push(mk_continue(std::move(loc)));
    } else if (auto *r = dyn_cast<ReturnStmt>(stmt)) {
      if (auto *rv = r->getRetValue()) {
        return stmts.push(mk_return(std::move(loc), trRValue(rv)));
      } else {
        return stmts.push(mk_return_void(std::move(loc)));
      }
    } else if (auto *g = dyn_cast<GotoStmt>(stmt)) {
      auto label = ctx.mk_ident(toStr(g->getLabel()->getName()), loc.clone());
      return stmts.push(mk_goto(std::move(loc), std::move(label)));
    } else if (auto *ls = dyn_cast<LabelStmt>(stmt)) {
      auto label =
          ctx.mk_ident(toStr(llvm::StringRef(ls->getName())), loc.clone());
      auto enss = Vec<Rc<ir::Expr>>::new_();
      auto subStmt = ls->getSubStmt();
      // Clang attaches __attribute__ to the label decl
      auto labelDecl = ls->getDecl();
      if (labelDecl->hasAttrs()) {
        for (auto attr : labelDecl->getAttrs()) {
          if (auto ens = isUnaryAttrOf(attr, "pal-ensures")) {
            enss.push(std::move(ens.value()));
          }
        }
      }
      // Also check if sub-statement is AttributedStmt
      if (auto attrStmt = dyn_cast<AttributedStmt>(subStmt)) {
        for (auto attr : attrStmt->getAttrs()) {
          if (auto ens = isUnaryAttrOf(attr, "pal-ensures")) {
            enss.push(std::move(ens.value()));
          }
        }
        subStmt = attrStmt->getSubStmt();
      }
      stmts.push(mk_label(std::move(loc), std::move(label), std::move(enss)));
      return trStmt(stmts, subStmt);
    } else if (auto *ds = dyn_cast<DeclStmt>(stmt)) {
      for (auto d : ds->decls()) {
        auto dloc = getRange(d->getSourceRange());
        if (auto vd = dyn_cast<VarDecl>(d)) {
          auto id = ctx.mk_ident(toStr(vd->getName()), dloc.clone());
          auto qt = vd->getType();
          if (auto *vat =
                  dyn_cast<VariableArrayType>(qt.IgnoreParens().getTypePtr())) {
            auto elemTy =
                trQualType(vat->getElementType(), vd->getSourceRange());
            auto sizeExpr = trRValue(vat->getSizeExpr());
            stmts.push(mk_decl_stack_array(dloc.clone(), id.clone(),
                                           std::move(elemTy),
                                           std::move(sizeExpr)));
          } else {
            auto ty =
                trTypeAttrs(vd->getAttrs(),
                            trQualType(vd->getType(), vd->getSourceRange()));
            stmts.push(mk_var_decl(dloc.clone(), id.clone(), std::move(ty)));
            if (vd->hasInit()) {
              stmts.push(mk_assign(dloc.clone(),
                                   mk_lvalue_var(dloc.clone(), id.clone()),
                                   trRValue(vd->getInit())));
            }
          }
        } else {
          reportUnsupported(d->getSourceRange(), dloc,
                            "unsupported variable declaration ",
                            d->getDeclKindName());
          stmts.push(mk_stmt_err(dloc.clone()));
        }
      }
      return rust::Unit();
    } else if (auto *p = dyn_cast<ParenExpr>(stmt)) {
      return trStmt(stmts, p->getSubExpr());
    } else if (auto *comp = dyn_cast<CompoundStmt>(stmt)) {
      // TODO: scope
      for (auto stmt : comp->body())
        trStmt(stmts, stmt);
      return rust::Unit();
    } else if (auto *c = dyn_cast<CallExpr>(stmt)) {
      // Intercept __pal_c_assert(expr) — translated from C assert()
      if (auto fd = c->getDirectCallee()) {
        if (fd->getName() == "__pal_c_assert" && c->getNumArgs() == 1) {
          auto val = trRValue(c->getArg(0));
          // Cast to bool — elab will convert to slprop via with_pure
          auto boolVal = mk_rvalue_cast(loc.clone(), std::move(val),
                                        mk_bool_type(loc.clone()));
          // Wrap in if (pal_c_assert_enabled()) to expose
          // side-effect differences when assertions are disabled.
          auto enabledFn = ctx.mk_ident(
              toStr(StringRef("pal_c_assert_enabled")), loc.clone());
          auto enabledArgs = Vec<Rc<ir::Expr>>::new_();
          auto enabledCall = mk_rvalue_fncall(loc.clone(), std::move(enabledFn),
                                              std::move(enabledArgs));
          auto thenStmts = Vec<Rc<ir::Stmt>>::new_();
          thenStmts.push(mk_assert(loc.clone(), std::move(boolVal)));
          auto elseStmts = Vec<Rc<ir::Stmt>>::new_();
          return stmts.push(mk_if(std::move(loc), std::move(enabledCall),
                                  std::move(thenStmts), std::move(elseStmts),
                                  Vec<Rc<ir::Expr>>::new_()));
        }
      }
      return stmts.push(mk_call(std::move(loc), trRValue(c)));
    } else if (auto *se = dyn_cast<StmtExpr>(stmt)) {
      // _assert(p) expands to ({ __attribute__((annotate("pal-assert",
      // ...))) {} })
      // _ghost_stmt(p) expands similarly with "pal-ghost-stmt"
      if (auto *comp = dyn_cast<CompoundStmt>(se->getSubStmt())) {
        for (auto s : comp->body()) {
          if (auto *attr = dyn_cast<AttributedStmt>(s)) {
            for (auto a : attr->getAttrs()) {
              if (auto val = isUnaryAttrOf(a, "pal-assert")) {
                stmts.push(mk_assert(loc.clone(), std::move(val.value())));
                return rust::Unit();
              }
              if (auto ctr = isUnaryAttrCounter(a, "pal-ghost-stmt")) {
                stmts.push(
                    ctx.mk_ghost_stmt(loc.clone(), ctr.value(), snippets));
                return rust::Unit();
              }
            }
          }
        }
      }
    } else if (auto *cse = dyn_cast<CStyleCastExpr>(stmt)) {
      if (cse->getType()->isVoidType()) {
        // (void)expr — translate the sub-expression as a statement to
        // preserve any side effects (e.g. (void)x++).  Pure no-ops like
        // ((void)0) will naturally produce no IR.
        return trStmt(stmts, cse->getSubExpr());
      }
    } else if (dyn_cast<NullStmt>(stmt) || dyn_cast<IntegerLiteral>(stmt)) {
      return rust::Unit();
    }

    reportUnsupported(stmt->getSourceRange(), loc, "unsupported statement ",
                      stmt->getStmtClassName());
    return stmts.push(mk_stmt_err(std::move(loc)));
  }

  std::optional<Rc<ir::Expr>> isUnaryAttrOf(Attr const *attr,
                                            char const *name) {
    if (auto ann = dyn_cast<AnnotateAttr>(attr);
        ann && ann->args_size() == 1 && ann->getAnnotation() == name) {
      if (auto ctrVal = ann->args_begin()[0]->getIntegerConstantExpr(*astCtx)) {
        unsigned ctr = ctrVal->getZExtValue();
        return {ctx.parse_rvalue(getRange(attr->getRange()), ctr, snippets)};
      }
    }
    return {};
  }

  std::optional<unsigned> isUnaryAttrCounter(Attr const *attr,
                                             char const *name) {
    if (auto ann = dyn_cast<AnnotateAttr>(attr);
        ann && ann->args_size() == 1 && ann->getAnnotation() == name) {
      if (auto ctrVal = ann->args_begin()[0]->getIntegerConstantExpr(*astCtx)) {
        return {static_cast<unsigned>(ctrVal->getZExtValue())};
      }
    }
    return {};
  }

  rust::Unit HandleDecl(Decl *D) {
    if (auto *FD = dyn_cast<FunctionDecl>(D)) {
      // Include block
      if (FD->getName().starts_with("__pal_include_anchor")) {
        std::optional<unsigned> code;
        std::string modName;
        for (auto attr : FD->getAttrs()) {
          if (auto ann = dyn_cast<AnnotateAttr>(attr);
              ann && ann->getAnnotation() == "pal-includes" &&
              ann->args_size() == 2) {
            // First arg: string literal for module name
            if (auto strLit = dyn_cast<StringLiteral>(
                    ann->args_begin()[0]->IgnoreParenCasts())) {
              modName = strLit->getString().str();
            }
            // Second arg: __COUNTER__ for snippet index
            if (auto ctrVal =
                    ann->args_begin()[1]->getIntegerConstantExpr(*astCtx)) {
              unsigned ctr = ctrVal->getZExtValue();
              code = ctr;
            }
          }
        }
        auto loc = getRange(D->getSourceRange());
        if (code && !modName.empty()) {
          ctx.add_include(std::move(loc), toStr(modName), *code, snippets);
        } else {
          ctx.report_diag(std::move(loc), true,
                          "internal error: invalid INCLUDES encoding"_rs);
        }
        return {};
      }

      // Let decl block
      if (FD->getName().starts_with("__pal_let_anchor") ||
          FD->getName().starts_with("__pal_let_rec_anchor")) {
        bool is_rec = FD->getName().starts_with("__pal_let_rec_anchor");
        std::optional<unsigned> sig_ctr, body_ctr;
        for (auto attr : FD->getAttrs()) {
          if (auto ann = dyn_cast<AnnotateAttr>(attr);
              ann &&
              (ann->getAnnotation() == "pal-let" ||
               ann->getAnnotation() == "pal-let-rec") &&
              ann->args_size() == 2) {
            if (auto v0 =
                    ann->args_begin()[0]->getIntegerConstantExpr(*astCtx)) {
              sig_ctr = v0->getZExtValue();
            }
            if (auto v1 =
                    ann->args_begin()[1]->getIntegerConstantExpr(*astCtx)) {
              body_ctr = v1->getZExtValue();
            }
          }
        }
        auto loc = getRange(D->getSourceRange());
        if (sig_ctr && body_ctr) {
          ctx.add_let_decl(std::move(loc), is_rec, *sig_ctr, *body_ctr,
                           snippets);
        } else {
          ctx.report_diag(std::move(loc), true,
                          "internal error: invalid _let encoding"_rs);
        }
        return {};
      }

      // Let impure decl block
      if (FD->getName().starts_with("__pal_letimpure_anchor")) {
        std::optional<unsigned> sig_ctr, body_ctr;
        for (auto attr : FD->getAttrs()) {
          if (auto ann = dyn_cast<AnnotateAttr>(attr);
              ann && ann->getAnnotation() == "pal-letimpure" &&
              ann->args_size() == 2) {
            if (auto v0 =
                    ann->args_begin()[0]->getIntegerConstantExpr(*astCtx)) {
              sig_ctr = v0->getZExtValue();
            }
            if (auto v1 =
                    ann->args_begin()[1]->getIntegerConstantExpr(*astCtx)) {
              body_ctr = v1->getZExtValue();
            }
          }
        }
        auto loc = getRange(D->getSourceRange());
        if (sig_ctr && body_ctr) {
          ctx.add_letimpure_decl(std::move(loc), *sig_ctr, *body_ctr, snippets);
        } else {
          ctx.report_diag(std::move(loc), true,
                          "internal error: invalid _letimpure encoding"_rs);
        }
        return {};
      }

      // Type decl block
      if (FD->getName().starts_with("__pal_type_anchor")) {
        std::optional<unsigned> name_ctr, body_ctr;
        for (auto attr : FD->getAttrs()) {
          if (auto ann = dyn_cast<AnnotateAttr>(attr);
              ann && ann->getAnnotation() == "pal-type" &&
              ann->args_size() == 2) {
            if (auto v0 =
                    ann->args_begin()[0]->getIntegerConstantExpr(*astCtx)) {
              name_ctr = v0->getZExtValue();
            }
            if (auto v1 =
                    ann->args_begin()[1]->getIntegerConstantExpr(*astCtx)) {
              body_ctr = v1->getZExtValue();
            }
          }
        }
        auto loc = getRange(D->getSourceRange());
        if (name_ctr && body_ctr) {
          ctx.add_type_decl(std::move(loc), *name_ctr, *body_ctr, snippets);
        } else {
          ctx.report_diag(std::move(loc), true,
                          "internal error: invalid _type encoding"_rs);
        }
        return {};
      }

      // Regular function decl
      auto ident = getDeclName(FD);
      auto builder =
          DeclBuilder::new_(getRange(FD->getSourceRange()), ident.clone());
      for (auto param : FD->parameters()) {
        auto ty = trQualType(param->getType(), param->getSourceRange());
        ty = trTypeAttrs(param->getAttrs(), std::move(ty), param->getType(),
                         param->getSourceRange());
        auto mode = hasConsumesAttr(param->getAttrs())
                        ? ir::ParamMode::Consumed()
                    : hasOutAttr(param->getAttrs())
                        ? ir::ParamMode::Out()
                        : [&]() {
                            auto qt = param->getType().IgnoreParens();
                            if (qt.isConstQualified())
                              return ir::ParamMode::Const();
                            if (auto ptr = dyn_cast<PointerType>(qt)) {
                              if (ptr->getPointeeType().isConstQualified())
                                return ir::ParamMode::Const();
                            }
                            return ir::ParamMode::Regular();
                          }();
        if (param->getDeclName().isIdentifier() &&
            param->getName().size() > 0) {
          builder.arg(ctx.mk_ident(toStr(param->getName()),
                                   getRange(param->getSourceRange())),
                      std::move(ty), std::move(mode));
        } else {
          builder.arg_anon(std::move(ty), std::move(mode));
        }
      }
      builder.return_type(trTypeAttrs(
          FD->getAttrs(),
          trQualType(FD->getReturnType(), FD->getReturnTypeSourceRange())));
      for (auto attr : FD->getAttrs()) {
        if (FD->hasBody() && attr->isInherited())
          continue;
        if (auto req = isUnaryAttrOf(attr, "pal-requires")) {
          builder.requires(std::move(req.value()));
        }
        if (auto ens = isUnaryAttrOf(attr, "pal-ensures")) {
          builder.ensures(std::move(ens.value()));
        }
        if (auto dec = isUnaryAttrOf(attr, "pal-decreases")) {
          builder.decreases(std::move(dec.value()));
        }
        if (auto ann = dyn_cast<AnnotateAttr>(attr);
            ann && ann->getAnnotation() == "pal-pure" &&
            ann->args_size() == 0) {
          builder.set_pure();
        }
        if (auto ann = dyn_cast<AnnotateAttr>(attr);
            ann && ann->getAnnotation() == "pal-rec" && ann->args_size() == 0) {
          builder.set_rec();
        }
        if (auto ann = dyn_cast<AnnotateAttr>(attr);
            ann && ann->getAnnotation() == "pal-total" &&
            ann->args_size() == 0) {
          builder.set_total();
        }
        if (auto ctr = isUnaryAttrCounter(attr, "pal-ghost-arg")) {
          ctx.parse_ghost_arg(builder, getRange(attr->getRange()), ctr.value(),
                              snippets);
        }
      }
      if (FD->hasBody()) {
        return ctx.add_fn_defn(std::move(builder), trStmts(FD->getBody()));
      } else {
        return ctx.add_fn_decl(std::move(builder));
      }
    } else if (auto *TD = dyn_cast<TypedefDecl>(D)) {
      auto loc = getRange(TD->getSourceRange());
      auto id = ctx.mk_ident(toStr(TD->getName()), loc.clone());
      auto anon = AnonNameGen(TD->getName());
      auto type =
          trQualType(TD->getUnderlyingType(), TD->getSourceRange(), &anon);
      type = trTypeAttrs(TD->getAttrs(), std::move(type));
      bool isPointerView = false;
      if (TD->hasAttrs()) {
        for (auto *attr : TD->getAttrs()) {
          if (auto *ann = dyn_cast<AnnotateAttr>(attr)) {
            if (ann->getAnnotation() == "pal-pointer-view" &&
                ann->args_size() == 0) {
              isPointerView = true;
            }
          }
        }
      }
      return ctx.add_typedef(std::move(loc), std::move(id), std::move(type),
                             isPointerView);
    } else if (auto *RD = dyn_cast<RecordDecl>(D)) {
      auto loc = getRange(RD->getSourceRange());
      if (RD->getIdentifier()) {
        auto id = ctx.mk_ident(toStr(RD->getName()), loc.clone());
        auto anon = AnonNameGen(RD->getName());
        trRecordDecl(std::move(id), RD, &anon);
      } else {
        // TODO: forward struct decls
      }
      return {};
    } else if (auto *VD = dyn_cast<VarDecl>(D)) {
      auto loc = getRange(VD->getSourceRange());
      auto id = ctx.mk_ident(toStr(VD->getName()), loc.clone());
      auto ty = trQualType(VD->getType(), VD->getSourceRange());
      OptExpr init = VD->hasInit() ? OptExpr::Some(trRValue(VD->getInit()))
                                   : OptExpr::None();
      bool is_pure = VD->getType().isConstQualified() && VD->hasInit();
      bool opaque_to_smt = false;
      for (auto attr : VD->getAttrs()) {
        if (auto ann = dyn_cast<AnnotateAttr>(attr);
            ann && ann->getAnnotation() == "pal-pure" &&
            ann->args_size() == 0) {
          is_pure = true;
        }
        if (auto ann = dyn_cast<AnnotateAttr>(attr);
            ann && ann->getAnnotation() == "pal-opaque-to-smt" &&
            ann->args_size() == 0) {
          opaque_to_smt = true;
        }
      }
      return ctx.add_global_var(std::move(loc), std::move(id), std::move(ty),
                                std::move(init), is_pure, opaque_to_smt);
    } else if (dyn_cast<EnumDecl>(D)) {
      // Enum declarations need no IR representation;
      // constants are inlined as integer literals at use sites.
      return {};
    } else if (dyn_cast<StaticAssertDecl>(D)) {
      // _Static_assert / static_assert — compile-time check already
      // enforced by Clang; no Pulse representation needed.
      return {};
    }

    reportUnsupported(D->getSourceRange(), getRange(D->getSourceRange()),
                      "unsupported declaration ", D->getDeclKindName());
    return {};
  }
};

class PALAction : public SyntaxOnlyAction {
public:
  PALAction(RefMut<Ctx> c, RangeMap &m) : ctx(c), rangeMap(m) {}
  RefMut<Ctx> ctx;
  RangeMap &rangeMap;
  SnipMap snippets = SnipMap::default_();

  bool BeginSourceFileAction(CompilerInstance &CI) override {
    CI.getPreprocessor().addPPCallbacks(
        std::make_unique<MacroTracker>(rangeMap, snippets, CI));
    return SyntaxOnlyAction::BeginSourceFileAction(CI);
  }

  std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI,
                                                 StringRef InFile) override {
    return std::make_unique<PALConsumer>(ctx, rangeMap, snippets, CI);
  }

  void EndSourceFileAction() override {
    SyntaxOnlyAction::EndSourceFileAction();
  }
};

class PALActionFactory : public FrontendActionFactory {
public:
  PALActionFactory(RefMut<Ctx> c, RangeMap &m) : ctx(c), rangeMap(m) {}

  std::unique_ptr<FrontendAction> create() override {
    return std::make_unique<PALAction>(ctx, rangeMap);
  }

  RefMut<Ctx> ctx;
  RangeMap &rangeMap;
};

class PALDiagnosticConsumer : public DiagnosticConsumer {
public:
  PALDiagnosticConsumer(RefMut<Ctx> c, RangeMap &m) : ctx(c), rangeMap(m) {}
  RefMut<Ctx> ctx;
  RangeMap &rangeMap;

  void HandleDiagnostic(DiagnosticsEngine::Level DiagLevel,
                        const Diagnostic &Info) override {
    if (!Info.hasSourceManager())
      return;
    auto &sm = Info.getSourceManager();

    SourceLocation begin, end;

    if (Info.getNumRanges() > 0) {
      auto range = Info.getRange(0);
      begin = range.getBegin();
      end = range.getEnd();
    } else if (Info.getLocation().isValid()) {
      begin = Info.getLocation();
      end = begin;
    } else {
      return;
    }

    auto file_name =
        rangeMap.getFileName(sm, sm.getFileID(sm.getExpansionLoc(begin)));
    unsigned begin_line = sm.getExpansionLineNumber(begin);
    unsigned begin_col = sm.getExpansionColumnNumber(begin);
    unsigned end_line = sm.getExpansionLineNumber(end);
    unsigned end_col = sm.getExpansionColumnNumber(end);
    if (end_line == 0 || end_col == 0) {
      end_line = begin_line;
      end_col = begin_col;
    }
    llvm::SmallString<0> out;
    Info.FormatDiagnostic(out);
    ctx.report_diag(mk_original_location(std::move(file_name), begin_line,
                                         begin_col, end_line, end_col),
                    DiagLevel >= DiagnosticsEngine::Level::Error, toStr(out));
  }
};

#if LLVM_VERSION_MAJOR < 22
#define GetResourcesPath clang::driver::Driver::GetResourcesPath
#endif

std::string getBinaryForResourcesPath() {
  Dl_info info;
  if (dladdr((void *)static_cast<std::string (*)(StringRef)>(&GetResourcesPath),
             &info)) {
    return info.dli_fname;
  } else {
    return "/usr/bin/clang";
  }
}

std::string getResourcesPath() {
  return GetResourcesPath(getBinaryForResourcesPath());
}

llvm::vfs::Status mkStatus(Ref<rust::pal::vfs::VFSEntry> entry) {
  auto fileName = entry.get_file_name();
  llvm::sys::fs::UniqueID unique(0, (uint64_t)fileName.as_ptr());
  llvm::sys::TimePoint<> time;
  return llvm::vfs::Status(
      toStringRef(fileName), unique, time, 0, 0, entry.get_contents().len(),
      llvm::sys::fs::file_type::regular_file, llvm::sys::fs::perms::all_all);
}

class CtxVFSFile : public llvm::vfs::File {
  Rc<rust::pal::vfs::VFSEntry> entry;

public:
  CtxVFSFile(Rc<rust::pal::vfs::VFSEntry> &&e) : entry(std::move(e)) {}

  llvm::ErrorOr<llvm::vfs::Status> status() override {
    return mkStatus(entry.deref());
  }

  llvm::ErrorOr<std::unique_ptr<llvm::MemoryBuffer>>
  getBuffer(const Twine &Name, int64_t FileSize = -1,
            bool RequiresNullTerminator = true,
            bool IsVolatile = false) override {
    if (!RequiresNullTerminator)
      return llvm::MemoryBuffer::getMemBuffer(
          toStringRef(entry.deref().get_contents()),
          toStringRef(entry.deref().get_file_name()));

    return llvm::MemoryBuffer::getMemBufferCopy(
        toStringRef(entry.deref().get_contents()),
        toStringRef(entry.deref().get_file_name()));
  };

  std::error_code close() override { return {}; }

  llvm::ErrorOr<std::string> getName() override {
    return toString(entry.deref().get_file_name());
  }
};

class CtxVFS : public llvm::vfs::FileSystem {
  RefMut<Ctx> ctx;
  IntrusiveRefCntPtr<llvm::vfs::FileSystem> realFS;

public:
  CtxVFS(RefMut<Ctx> c) : ctx(c), realFS(llvm::vfs::getRealFileSystem()) {}

  static IntrusiveRefCntPtr<llvm::vfs::FileSystem> make(RefMut<Ctx> ctx) {
    return llvm::makeIntrusiveRefCnt<CtxVFS>(ctx);
  }

  llvm::ErrorOr<llvm::vfs::Status> status(const Twine &Path) override {
    auto res = ctx.read_vfs_file(toStr(Path.str()));
    if (!res.is_ok()) {
      // TODO: fallback for directories
      return realFS->status(Path);
    }
    return mkStatus(res.unwrap().deref());
  };

  llvm::ErrorOr<std::unique_ptr<llvm::vfs::File>>
  openFileForRead(const Twine &Path) override {
    auto res = ctx.read_vfs_file(toStr(Path.str()));
    if (!res.is_ok()) {
      return llvm::errc::no_such_file_or_directory;
    }
    return std::make_unique<CtxVFSFile>(res.unwrap());
  }

  llvm::vfs::directory_iterator dir_begin(const Twine &Dir,
                                          std::error_code &EC) override {
    return realFS->dir_begin(Dir, EC);
  }

  std::error_code setCurrentWorkingDirectory(const Twine &Path) override {
    return realFS->setCurrentWorkingDirectory(Path);
  }

  llvm::ErrorOr<std::string> getCurrentWorkingDirectory() const override {
    return realFS->getCurrentWorkingDirectory();
  }

  std::error_code getRealPath(const Twine &Path,
                              SmallVectorImpl<char> &Output) override {
    // TODO: implement using VFS
    return realFS->getRealPath(Path, Output);
  }

  bool exists(const Twine &Path) override {
    auto res = ctx.read_vfs_file(toStr(Path.str()));
    if (res.is_ok())
      return true;

    // TODO: fallback for directories
    return realFS->exists(Path);
  }

  std::error_code isLocal(const Twine &Path, bool &Result) override {
    Result = true;
    return {};
  }

  std::error_code makeAbsolute(SmallVectorImpl<char> &Path) const override {
    // TODO: implement using VFS
    return realFS->makeAbsolute(Path);
  }
};

static void parse_file(RefMut<Ctx> ctx) {
  std::string fileName = toString(ctx.get_input_file_name());
  std::vector<std::string> sourcePathList{fileName};

  std::string compDBErrMsg;
  auto compDB =
      CompilationDatabase::autoDetectFromSource(fileName, compDBErrMsg);
  std::vector<std::string> argsForCompDB;
  if (!compDB) {
    compDB = std::make_unique<FixedCompilationDatabase>(".", argsForCompDB);
  }

  ClangTool Tool(*compDB, sourcePathList,
                 std::make_shared<PCHContainerOperations>(), CtxVFS::make(ctx));

  RangeMap rangeMap(ctx);
  PALDiagnosticConsumer consumer(ctx, rangeMap);
  Tool.setDiagnosticConsumer(&consumer);

  // Tool.appendArgumentsAdjuster(OptionsParser->getArgumentsAdjuster());

  Tool.appendArgumentsAdjuster(getInsertArgumentAdjuster(
      {"-DC2PULSE", "-fno-builtin"}, ArgumentInsertPosition::BEGIN));
  Tool.appendArgumentsAdjuster(getInsertArgumentAdjuster(
      {"-resource-dir", getResourcesPath()}, ArgumentInsertPosition::BEGIN));

  // Add user-specified include paths
  size_t includePathCount = ctx.get_include_path_count();
  for (size_t i = 0; i < includePathCount; i++) {
    std::string incPath = "-I" + toString(ctx.get_include_path(i));
    Tool.appendArgumentsAdjuster(getInsertArgumentAdjuster(
        incPath.c_str(), ArgumentInsertPosition::BEGIN));
  }

  PALActionFactory factory(ctx, rangeMap);
  Tool.run(&factory);
}

namespace rust::exported_functions {
Unit parse_file(RefMut<Ctx> ctx) {
  ::parse_file(ctx);
  return {};
}
} // namespace rust::exported_functions