#include "pal.h"
/* Pointer casts between an overlay union and a member that is itself an
   overlay union of the same size and alignment: the layered-request idiom,
   where a derived request is passed to the base layer as its base type and
   recovered from it with a containing-record cast. */
#include <stdint.h>
#include <stddef.h>

typedef struct _COMMON { uint64_t Owner; uint32_t Status; uint32_t Flags; } COMMON;
typedef union _overlay _BASE { COMMON Common; uint8_t Raw[16]; } BASE;
typedef struct _PARAMS { uint32_t Count; } PARAMS;
typedef union _overlay _DERIVED { PARAMS Params; BASE Base; } DERIVED;

void Base_SetStatus(BASE* B, uint32_t S)
    _requires(B->Common._active)
    _ensures(B->Common._active && B->Common.Status == S)
{ B->Common.Status = S; }

uint32_t Base_GetStatus(const BASE* B)
    _requires(B->Common._active)
    _ensures(return == B->Common.Status)
{ return B->Common.Status; }

/* Down-cast through a local and a mutating call. */
void Derived_SetStatus(DERIVED* D, uint32_t S)
    _requires(D->Base._active && D->Base.Common._active)
    _ensures(D->Base._active && D->Base.Common._active && D->Base.Common.Status == S)
{
    BASE* b = (BASE*)D;
    Base_SetStatus(b, S);
}

/* A read-only call through the cast keeps the whole value. */
uint32_t Derived_GetStatus(const DERIVED* D)
    _requires(D->Base._active && D->Base.Common._active)
    _ensures(return == D->Base.Common.Status)
{
    return Base_GetStatus((const BASE*)D);
}

/* Up-cast: the caller owns a BASE and gets back the derived view. */
DERIVED* Derived_FromBase(BASE* B)
    _ensures(return == (DERIVED*)B)
{
    return (DERIVED*)B;
}

/* Up-cast at a call: a base-layer caller hands its request to a function of
   the derived view and sees the effect in its own view. */
void Base_SetViaDerived(BASE* B)
    _requires(B->Common._active)
    _ensures(B->Common._active && B->Common.Status == 7u)
{
    Derived_SetStatus((DERIVED*)B, 7u);
}

/* Struct arms: reached directly or through a local, for reading (which
   gives the union back with exactly its bytes, padding included, as a
   `preserves` needs) and for writing. */
typedef struct _SEQ { uint64_t Value; } SEQ;
typedef struct _ARGS { uint32_t Count; SEQ Seq; } ARGS;
typedef union _overlay _REQ { ARGS Args; uint8_t Raw[16]; } REQ;

uint64_t Seq_Get(const SEQ* s) _ensures(return == s->Value) { return s->Value; }
void Seq_Set(SEQ* s, uint64_t v) _ensures(s->Value == v) { s->Value = v; }

uint64_t Direct_Get(const REQ* r)
    _requires(r->Args._active) _ensures(return == r->Args.Seq.Value)
{ return Seq_Get(&r->Args.Seq); }

void Direct_Set(REQ* r, uint64_t v)
    _requires(r->Args._active) _ensures(r->Args._active && r->Args.Seq.Value == v)
{ Seq_Set(&r->Args.Seq, v); }

uint64_t Local_Get(const REQ* r)
    _requires(r->Args._active) _ensures(return == r->Args.Seq.Value)
{ const ARGS* p = &r->Args; return Seq_Get(&p->Seq); }

void Local_Set(REQ* r, uint64_t v)
    _requires(r->Args._active) _ensures(r->Args._active && r->Args.Seq.Value == v)
{ ARGS* p = &r->Args; Seq_Set(&p->Seq, v); }

void Local_SetCount(REQ* r, uint32_t c)
    _requires(r->Args._active) _ensures(r->Args._active && r->Args.Count == c)
{ ARGS* p = &r->Args; p->Count = c; }

uint32_t Direct_GetCount(const REQ* r)
    _requires(r->Args._active) _ensures(return == r->Args.Count)
{ return r->Args.Count; }

uint32_t Local_GetCount(const REQ* r)
    _requires(r->Args._active) _ensures(return == r->Args.Count)
{ const ARGS* p = &r->Args; return p->Count; }

uint64_t Local_GetValue(const REQ* r)
    _requires(r->Args._active) _ensures(return == r->Args.Seq.Value)
{ const ARGS* p = &r->Args; return p->Seq.Value; }

/* The alias declared first and bound later, as C89-style code does. */
uint64_t Late_Get(const REQ* r)
    _requires(r->Args._active) _ensures(return == r->Args.Seq.Value)
{
    const ARGS* p = NULL;
    p = &r->Args;
    return Seq_Get(&p->Seq);
}

void Late_Set(REQ* r, uint64_t v)
    _requires(r->Args._active) _ensures(r->Args._active && r->Args.Seq.Value == v)
{
    ARGS* p = NULL;
    uint64_t w = v;
    p = &r->Args;
    Seq_Set(&p->Seq, w);
}
