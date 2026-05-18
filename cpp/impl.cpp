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

  void trRecordDecl(Rc<ir::Ident> ident, RecordDecl *decl,
                    AnonNameGen *liftStructs) {
    if (!decl->isCompleteDefinition()) {
      if (decl->getTagKind() == TagTypeKind::Struct) {
        auto loc = getRange(decl->getSourceRange());
        ctx.add_struct_decl(std::move(loc), std::move(ident));
      }
      return;
    }
    if (!alreadyDefined.insert(decl).second)
      return;
    auto loc = getRange(decl->getSourceRange());
    auto builder = DeclBuilder::new_(loc.clone(), ident.clone());
    if (decl->getTagKind() == TagTypeKind::Struct) {
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
        auto floc = getRange(f->getSourceRange());
        if (!f->getIdentifier()) {
          reportUnsupported(f->getSourceRange(), floc,
                            "unsupported anonymous field names", "");
        }
        builder.field(ctx.mk_ident(toStr(f->getName()), std::move(floc)),
                      trTypeAttrs(f->getAttrs(),
                                  trQualType(f->getType(), f->getSourceRange(),
                                             liftStructs)));
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
        auto floc = getRange(f->getSourceRange());
        if (!f->getIdentifier()) {
          reportUnsupported(f->getSourceRange(), floc,
                            "unsupported anonymous field names", "");
        }
        builder.field(ctx.mk_ident(toStr(f->getName()), std::move(floc)),
                      trTypeAttrs(f->getAttrs(),
                                  trQualType(f->getType(), f->getSourceRange(),
                                             liftStructs)));
      }
      ctx.add_union(std::move(builder));
    } else {
      reportUnsupported(decl->getSourceRange(), loc, "unsupported record kind",
                        "");
    }
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
      return mk_pointer_unknown(
          std::move(loc),
          trQualType(ptr->getPointeeType(), /*TODO*/ range, liftStructs));
    } else if (auto adj = dyn_cast<AdjustedType>(t)) {
      return trQualType(adj->getOriginalType(), range, liftStructs);
    } else if (auto arr = dyn_cast<ArrayType>(t)) {
      return mk_pointer_array(
          std::move(loc),
          trQualType(arr->getElementType(), /* TODO */ range, liftStructs));
    } else if (auto rec = dyn_cast<RecordType>(t)) {
      auto decl = rec->getDecl();
      Rc<ir::Ident> name;
      if (decl->getIdentifier()) {
        structNames.emplace(decl, decl->getName().str());
        name = ctx.mk_ident(toStr(decl->getName()), loc.clone());
      } else if (liftStructs) {
        auto nameStr = liftStructs->next();
        structNames.emplace(decl, nameStr);
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
    if (t->isSignedIntegerType() || t->isUnsignedIntegerType()) {
      bool isSigned = t->isSignedIntegerType();
      unsigned width = astCtx->getIntWidth(t);
      return mk_int_type(std::move(loc), isSigned, width);
    }

    reportUnsupported(range, loc, "unsupported type ", t->getTypeClassName());
    return mk_type_err(std::move(loc));
  }

  Rc<ir::Type> trTypeAttrs(AttrVec const &attrs, Rc<ir::Type> &&ty) {
    for (auto it = attrs.rbegin(); it != attrs.rend(); ++it) {
      if (auto ann = dyn_cast<AnnotateAttr>(*it)) {
        auto loc = getRange(ann->getRange());
        if (auto ref = isUnaryAttrOf(ann, "pal-refine")) {
          ty = mk_type_refine(std::move(loc), std::move(ty),
                              std::move(ref.value()));
        } else if (auto ref = isUnaryAttrOf(ann, "pal-refine-always")) {
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
        } else if (ann->getAnnotation() == "pal-array" &&
                   ann->args_size() == 0) {
          ty = mk_type_array(std::move(loc), std::move(ty));
        } else if (ann->getAnnotation() == "pal-arrayptr" &&
                   ann->args_size() == 0) {
          ty = mk_type_arrayptr(std::move(loc), std::move(ty));
        }
      }
    }
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

    if (auto dre = dyn_cast<DeclRefExpr>(e)) {
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
      auto id = ctx.mk_ident(toStr(m->getMemberDecl()->getName()), loc.clone());
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
    auto *rec = dyn_cast<RecordType>(qt.getTypePtr());
    if (!rec) {
      reportUnsupported(range, loc,
                        "unsupported initializer list for non-record type", "");
      return mk_rvalue_err(std::move(loc), trQualType(init->getType(), range));
    }
    auto *decl = rec->getDecl();
    auto it = structNames.find(decl);
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
      auto fieldName = ctx.mk_ident(toStr(field->getName()), std::move(floc));
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
      auto floc = getRange(fieldInit->getSourceRange());
      auto fieldName = ctx.mk_ident(toStr(field->getName()), std::move(floc));
      builder.field(std::move(fieldName), trRValue(fieldInit));
    }
    return builder.build();
  }

  Rc<ir::Expr> trRValue(Expr *e) {
    auto loc = getRange(e->getSourceRange());

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
      case CK_ArrayToPointerDecay:
        return mk_rvalue_lvalue(std::move(loc), trLValue(ic->getSubExpr()));
      case CK_IntegralCast:
      case CK_IntegralToBoolean:
      case CK_PointerToBoolean:
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
            // Detect calloc(n, sizeof(T))
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
    } else if (auto uo = dyn_cast<UnaryOperator>(e)) {
      switch (uo->getOpcode()) {
      case UO_AddrOf:
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
        auto fn = ctx.mk_ident(toStr(fd->getName()),
                               getRange(c->getCallee()->getSourceRange()));
        auto args = Vec<Rc<ir::Expr>>::new_();
        for (auto arg : c->arguments()) {
          args.push(trRValue(arg));
        }
        return mk_rvalue_fncall(std::move(loc), std::move(fn), std::move(args));
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
      // Other DeclRefExpr in rvalue context: treat as lvalue read
      return mk_rvalue_lvalue(std::move(loc), trLValue(e));
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
      return stmts.push(mk_if(loc.clone(), trRValue(i->getCond()),
                              trStmts(i->getThen()), trStmts(i->getElse())));
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
      // Desugar: do { body } while (cond)
      //      --> bool flag = true;
      //          while (flag || cond) { flag = false; body; }
      // If _do_while_first(name) is provided, use that name for the flag.

      // Extract annotations and check for _do_while_first
      auto body = d->getBody();
      auto invs = Vec<Rc<ir::Expr>>::new_();
      auto reqs = Vec<Rc<ir::Expr>>::new_();
      auto enss = Vec<Rc<ir::Expr>>::new_();
      std::string flagName;
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
            }
          }
        }
        body = attrBody->getSubStmt();
      }

      if (flagName.empty()) {
        static int doCounter = 0;
        flagName = "__do_first_" + std::to_string(doCounter++);
      }
      auto flagId = ctx.mk_ident(toStr(flagName), loc.clone());

      // bool flag; flag = true;
      stmts.push(
          mk_var_decl(loc.clone(), flagId.clone(), mk_bool_type(loc.clone())));
      stmts.push(mk_assign(loc.clone(),
                           mk_lvalue_var(loc.clone(), flagId.clone()),
                           mk_bool_lit(loc.clone(), true)));

      // while condition: flag || cond
      auto flagRead = mk_rvalue_lvalue(
          loc.clone(), mk_lvalue_var(loc.clone(), flagId.clone()));
      auto whileCond =
          mk_rvalue_binop(loc.clone(), ir::BinOp::LogOr(), std::move(flagRead),
                          trRValue(d->getCond()));

      // Add _live(flag) to invariants (skip if user provided _do_while_first,
      // since user is expected to include it in their own invariant)
      if (flagName.find("__do_first_") == 0) {
        invs.push(
            mk_live(loc.clone(), mk_lvalue_var(loc.clone(), flagId.clone())));
      }

      // Build body: flag = false; original_body;
      auto bodyStmts = Vec<Rc<ir::Stmt>>::new_();
      bodyStmts.push(mk_assign(loc.clone(),
                               mk_lvalue_var(loc.clone(), flagId.clone()),
                               mk_bool_lit(loc.clone(), false)));
      trStmt(bodyStmts, body);

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

      // Create scrutinee temp variable
      static int switchCounter = 0;
      auto scrutName = "__switch_scrut_" + std::to_string(switchCounter);
      auto scrutId = ctx.mk_ident(toStr(scrutName), loc.clone());
      stmts.push(mk_var_decl(loc.clone(), scrutId.clone(), std::move(scrutTy)));
      stmts.push(mk_assign(loc.clone(),
                           mk_lvalue_var(loc.clone(), scrutId.clone()),
                           std::move(scrutRval)));

      // Create hit and brk flag variables
      auto hitName = "__switch_hit_" + std::to_string(switchCounter);
      auto brkName = "__switch_brk_" + std::to_string(switchCounter);
      switchCounter++;
      auto hitId = ctx.mk_ident(toStr(hitName), loc.clone());
      auto brkId = ctx.mk_ident(toStr(brkName), loc.clone());
      auto boolTy = mk_bool_type(loc.clone());

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

      // Set switchBreakId so BreakStmt sets flag
      auto savedSwitchBreak = switchBreakId;
      auto brkIdHeap = new Rc<ir::Ident>(brkId.clone());
      switchBreakId = brkIdHeap;

      // Collect cases from the switch body
      auto *body = sw->getBody();
      auto *comp = dyn_cast<CompoundStmt>(body);
      if (!comp) {
        reportUnsupported(body->getSourceRange(), loc,
                          "switch body must be a compound statement", "");
        delete switchBreakId;
        switchBreakId = savedSwitchBreak;
        return {};
      }

      // Walk the compound statement collecting case/default groups
      bool seenDefault = false;
      for (auto *child : comp->body()) {
        auto childLoc = getRange(child->getSourceRange());

        if (auto *cs = dyn_cast<CaseStmt>(child)) {
          if (seenDefault) {
            reportUnsupported(cs->getSourceRange(), childLoc,
                              "default must be the last case in switch", "");
            break;
          }

          // Collect all case values from chained cases (case 1: case 2: ...)
          // and find the final sub-statement
          std::vector<Expr *> caseValues;
          Stmt *caseBody = child;
          while (auto *innerCs = dyn_cast<CaseStmt>(caseBody)) {
            caseValues.push_back(innerCs->getLHS());
            caseBody = innerCs->getSubStmt();
          }

          // Build match condition: scrut == v1 || scrut == v2 || ...
          Rc<ir::Expr> matchCond = mk_bool_lit(childLoc.clone(), false);
          for (auto *cv : caseValues) {
            auto scrutRead = mk_rvalue_lvalue(
                childLoc.clone(),
                mk_lvalue_var(childLoc.clone(), scrutId.clone()));
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
          if (caseBody)
            trStmt(thenStmts, caseBody);

          auto elseStmts = Vec<Rc<ir::Stmt>>::new_();
          stmts.push(mk_if(std::move(childLoc), std::move(cond),
                           std::move(thenStmts), std::move(elseStmts)));

        } else if (dyn_cast<DefaultStmt>(child)) {
          seenDefault = true;
          auto *ds = dyn_cast<DefaultStmt>(child);

          // Condition: !brk
          auto notBrk = mk_rvalue_unop(
              childLoc.clone(), ir::UnOp::Not(),
              mk_rvalue_lvalue(childLoc.clone(),
                               mk_lvalue_var(childLoc.clone(), brkId.clone())));

          auto thenStmts = Vec<Rc<ir::Stmt>>::new_();
          thenStmts.push(mk_assign(
              childLoc.clone(), mk_lvalue_var(childLoc.clone(), hitId.clone()),
              mk_bool_lit(childLoc.clone(), true)));
          if (ds->getSubStmt())
            trStmt(thenStmts, ds->getSubStmt());

          auto elseStmts = Vec<Rc<ir::Stmt>>::new_();
          stmts.push(mk_if(std::move(childLoc), std::move(notBrk),
                           std::move(thenStmts), std::move(elseStmts)));

        } else {
          // Bare statement outside case/default — translate directly
          trStmt(stmts, child);
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
          if (auto *cat =
                  dyn_cast<ConstantArrayType>(qt.IgnoreParens().getTypePtr())) {
            auto elemTy =
                trQualType(cat->getElementType(), vd->getSourceRange());
            auto sizeVal = cat->getSize().getZExtValue();
            auto sizeStr = std::to_string(sizeVal);
            auto sizeExpr = mk_int_lit(dloc.clone(), mk_bigint(toStr(sizeStr)),
                                       mk_sizet(dloc.clone()));
            stmts.push(mk_decl_stack_array(dloc.clone(), id.clone(),
                                           std::move(elemTy),
                                           std::move(sizeExpr)));
          } else if (auto *vat = dyn_cast<VariableArrayType>(
                         qt.IgnoreParens().getTypePtr())) {
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
                                  std::move(thenStmts), std::move(elseStmts)));
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
        ty = trTypeAttrs(param->getAttrs(), std::move(ty));
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
      return ctx.add_typedef(std::move(loc), std::move(id), std::move(type));
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
      for (auto attr : VD->getAttrs()) {
        if (auto ann = dyn_cast<AnnotateAttr>(attr);
            ann && ann->getAnnotation() == "pal-pure" &&
            ann->args_size() == 0) {
          is_pure = true;
        }
      }
      return ctx.add_global_var(std::move(loc), std::move(id), std::move(ty),
                                std::move(init), is_pure);
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