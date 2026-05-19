#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>
#include "DPE.h"
#include "EngineCore.h"

_include_pulse(DPE_context_full_data,
  $declare(context_t s)
  [@@erasable]
  noeq type context_full_data =
    | PL_Engine of (Seq.seq (option UInt8.t))
    | PL_L0 of (Seq.seq (option UInt8.t))
    | PL_L1 // tbd

  let tag_relation ($(s): $type(context_t)) (h: context_full_data) : prop =
    match $(s.tag) with
    | 0uy -> $(s.payload.uds._active) /\ PL_Engine? h
    | 1uy -> $(s.payload.cdi._active) /\ PL_L0? h
    | 2uy -> $(s.payload.l1_context._active) /\ PL_L1? h
    | _ -> False
)

_include_pulse(DPE_predicates,
  $declare(context_t s)
  [@@pulse_eager_unfold]
  let uds_pred (uds: $type(uds_array)) (uds_data: Seq.seq (option UInt8.t)) : slprop =
    exists* mask. ty_uds_array__pred uds 1.0R uds_data mask ** freeable_array uds

  [@@pulse_eager_unfold]
  let cdi_pred (cdi: $type(dice_digest)) (cdi_data: Seq.seq (option UInt8.t)) : slprop =
    exists* mask. ty_dice_digest__pred cdi 1.0R cdi_data mask ** freeable_array cdi

  let context_full_pred ([@@@mkey] $(s): $type(context_t)) (h: DPE_context_full_data.context_full_data) : slprop =
    match $(s.payload), h with
    | $field(u_context_t::uds) uds_ptr, DPE_context_full_data.PL_Engine uds_data ->
      uds_pred uds_ptr uds_data
    | $field(u_context_t::cdi) cdi_ptr, DPE_context_full_data.PL_L0 cdi_data ->
      cdi_pred cdi_ptr cdi_data
    | $field(u_context_t::l1_context) l1, DPE_context_full_data.PL_L1 ->
      emp
    | _ -> pure False

  let engine_state ($(s): $type(context_t)) #x =
    observe (context_full_pred $(s)) #x

  ghost fn elim_context_full_pred_uds ($(s): $type(context_t)) (#h: DPE_context_full_data.context_full_data)
    requires with_pure (DPE_context_full_data.tag_relation $(s) h /\ DPE_context_full_data.PL_Engine? h)
    requires context_full_pred $(s) h
    ensures uds_pred $(s.payload.uds) (DPE_context_full_data.PL_Engine?._0 h)
  {
    unfold context_full_pred;
    rewrite each $(s.payload) as $field(u_context_t::uds) $(s.payload.uds);
    rewrite each h as DPE_context_full_data.PL_Engine (DPE_context_full_data.PL_Engine?._0 h);
  }
  
  ghost fn elim_context_full_pred_cdi ($(s): $type(context_t)) (#h: DPE_context_full_data.context_full_data)
    requires with_pure (DPE_context_full_data.tag_relation $(s) h /\ DPE_context_full_data.PL_L0? h)
    requires context_full_pred $(s) h
    ensures cdi_pred $(s.payload.cdi) (DPE_context_full_data.PL_L0?._0 h)
  {
    unfold context_full_pred;
    rewrite each $(s.payload) as $field(u_context_t::cdi) $(s.payload.cdi);
    rewrite each h as DPE_context_full_data.PL_L0 (DPE_context_full_data.PL_L0?._0 h);
  }
  
  ghost fn elim_context_full_pred_l1 ($(s): $type(context_t)) (#h: DPE_context_full_data.context_full_data)
    requires with_pure (DPE_context_full_data.tag_relation $(s) h /\ DPE_context_full_data.PL_L1? h)
    requires context_full_pred $(s) h
  {
    unfold context_full_pred;
    rewrite each $(s.payload) as $field(u_context_t::l1_context) $(s.payload.l1_context);
    rewrite each h as DPE_context_full_data.PL_L1;
  }

  ghost fn intro_context_full_pred_uds ($(s): $type(context_t)) #uds
    requires with_pure (DPE_context_full_data.tag_relation $(s) (DPE_context_full_data.PL_Engine uds))
    requires uds_pred $(s.payload.uds) uds
    ensures context_full_pred $(s) (DPE_context_full_data.PL_Engine uds)
  {
    rewrite uds_pred $(s.payload.uds) uds
      as context_full_pred $(s) (DPE_context_full_data.PL_Engine uds);
  }

  ghost fn intro_context_full_pred_cdi ($(s): $type(context_t)) #cdi
    requires with_pure (DPE_context_full_data.tag_relation $(s) (DPE_context_full_data.PL_L0 cdi))
    requires cdi_pred $(s.payload.cdi) cdi
    ensures context_full_pred $(s) (DPE_context_full_data.PL_L0 cdi)
  {
    rewrite cdi_pred $(s.payload.cdi) cdi
      as context_full_pred $(s) (DPE_context_full_data.PL_L0 cdi);
  }
)

void memcpy_(size_t len, _array const uint8_t *a1, _out _array uint8_t *a2)
  _preserves(a1._length == len)
  _preserves(a2._length == len)
  _ensures((bool) _inline_pulse(array_value_of $(a2) == array_value_of $(a1)))
{
  _ghost_stmt(admit());
}

_refine((_slprop) _inline_pulse(
  exists* state.
    pure (DPE_context_full_data.tag_relation $(*this) state) **
    DPE_predicates.context_full_pred $(*this) state))
typedef context_t *context_obj;

_allocated context_obj init_engine_context(const uds_array uds)
  _ensures((bool) _inline_pulse(DPE_predicates.engine_state $(*return) == DPE_context_full_data.PL_Engine (array_value_of $(uds))))
{
  uint8_t *uds_buf = (uint8_t*)malloc(UDS_LEN * sizeof(uint8_t));
  memcpy_(UDS_LEN, uds, uds_buf);
  context_t *ctx = (context_t*)malloc(sizeof(context_t));
  *ctx = (context_t) {
    .tag = ENGINE_CONTEXT,
    .payload = (u_context_t) { .uds = uds_buf },
  };
  _ghost_stmt(DPE_predicates.intro_context_full_pred_uds $(*ctx));
  return ctx;
}

_include_pulse (DPE_ghost_helpers,
  ghost fn elim_maybe_true (p:slprop)
  requires maybe _true_ p
  ensures p
  { unfold maybe; }
)

void init_l0_context(context_obj ctx, const dice_digest cdi)
  _requires((bool) _inline_pulse(DPE_context_full_data.PL_Engine? (DPE_predicates.engine_state $(*ctx))))
  _ensures((bool) _inline_pulse(DPE_predicates.engine_state $(*ctx) == DPE_context_full_data.PL_L0 (array_value_of $(cdi))))
{
  uint8_t *cdi_buf = (uint8_t*)malloc(DICE_DIGEST_LEN * sizeof(uint8_t));
  memcpy_(DICE_DIGEST_LEN, cdi, cdi_buf);
  _ghost_stmt(DPE_predicates.elim_context_full_pred_uds $(*ctx));
  uint8_t* uds_buf = ctx->payload.uds;
  free(uds_buf);
  ctx->tag = 1;
  ctx->payload.cdi = cdi_buf;
  _ghost_stmt(DPE_predicates.intro_context_full_pred_cdi $(*ctx));
  return;
}

void destroy_uds_context(_consumes _allocated context_obj ctx)
  _requires(ctx->tag == 0)
{
  _ghost_stmt(DPE_predicates.elim_context_full_pred_uds $(*ctx));
  uint8_t* uds_buf = ctx->payload.uds;
  free(uds_buf);
  free(ctx);
  return;
}

void mk_l0_context(context_obj ctx, _consumes _allocated_array dice_digest cdi)
  _requires(ctx->tag == 0)
  _ensures((bool) _inline_pulse(DPE_predicates.engine_state $(*ctx) == DPE_context_full_data.PL_L0 (old (array_value_of $(cdi)))))
{
  _assert(cdi._length == DICE_DIGEST_LEN);
  _ghost_stmt(DPE_predicates.elim_context_full_pred_uds $(*ctx));
  uint8_t* uds_buf = ctx->payload.uds;
  free(uds_buf);
  ctx->tag = 1;
  ctx->payload.cdi = cdi;
  _ghost_stmt(DPE_predicates.intro_context_full_pred_cdi $(*ctx));
}

bool derive_child_from_context(context_obj ctx, const engine_record_t *record)
  _requires(ctx->tag == 0)
  _ensures(return ==> (bool) _inline_pulse(DPE_context_full_data.PL_L0? (DPE_predicates.engine_state $(*ctx))))
  _ensures(!return ==> (bool) _inline_pulse(DPE_predicates.engine_state $(*ctx) == old (DPE_predicates.engine_state $(*ctx))))
{
  _ghost_stmt(DPE_predicates.elim_context_full_pred_uds $(*ctx));
  uint8_t *cdi_buf = (uint8_t*)calloc(DICE_DIGEST_LEN, sizeof(uint8_t));
  _assert(cdi_buf._length == DICE_DIGEST_LEN);
  bool ok = engine_main(cdi_buf, ctx->payload.uds, record);
  if (ok) {
    _ghost_stmt(DPE_predicates.intro_context_full_pred_uds $(*ctx));
    mk_l0_context(ctx, cdi_buf);
    return true;
  } else {
    _ghost_stmt(DPE_predicates.intro_context_full_pred_uds $(*ctx));
    free(cdi_buf);
    return false;
  }
}