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
)

_type(context_full_data, DPE_context_full_data.context_full_data)

_let(bool tag_relation(context_t s, context_full_data h),
  _inline_pulse(
    let open DPE_context_full_data in
    match $(s.tag) with
    | 0uy -> $(s.payload.uds._active) /\ PL_Engine? $(h)
    | 1uy -> $(s.payload.cdi._active) /\ PL_L0? $(h)
    | 2uy -> $(s.payload.l1_context._active) /\ PL_L1? $(h)
    | _ -> False))

_include_pulse(DPE_predicates0,
  $declare(context_t s)
  $declare(context_full_data h)
  open DPE_context_full_data

  [@@pulse_eager_unfold]
  let uds_pred (uds: $type(uds_array)) (uds_data: Seq.seq (option UInt8.t)) : slprop =
    exists* (aspec: full_array_spec UInt8.t).
      Typedef_uds_array.ty_uds_array__pred uds 1.0R aspec **
      pure (array_spec_seq aspec == uds_data) **
      freeable_array uds

  [@@pulse_eager_unfold]
  let cdi_pred (cdi: $type(dice_digest)) (cdi_data: Seq.seq (option UInt8.t)) : slprop =
    exists* (aspec: full_array_spec UInt8.t).
      Typedef_dice_digest.ty_dice_digest__pred cdi 1.0R aspec **
      pure (array_spec_seq aspec == cdi_data) **
      freeable_array cdi
)

_let(_slprop context_full_pred(context_t s, context_full_data h),
  _inline_pulse((
    let open DPE_predicates0 in
    let open DPE_context_full_data in
    match $(s.payload), $(h) with
    | $field(u_context_t::uds) uds_ptr, PL_Engine uds_data ->
      uds_pred uds_ptr uds_data
    | $field(u_context_t::cdi) cdi_ptr, PL_L0 cdi_data ->
      cdi_pred cdi_ptr cdi_data
    | $field(u_context_t::l1_context) l1, PL_L1 ->
      emp
    | _ -> pure False)))

_include_pulse(DPE_predicates,
  $declare(context_t s)
  $declare(context_full_data h)
  open DPE_predicates0
  open DPE_context_full_data

  let engine_state ($(s): $type(context_t)) #x =
    observe (fun $(h) -> $(context_full_pred(s,h))) #x

  ghost fn elim_context_full_pred_uds ($(s): $type(context_t)) (#$(h): context_full_data)
    requires with_pure ($(tag_relation(s, h)) /\ PL_Engine? $(h))
    requires $(context_full_pred(s, h))
    ensures uds_pred $(s.payload.uds) (PL_Engine?._0 $(h))
  {
    unfold Let_context_full_pred.func_context_full_pred _ _;
    rewrite each $(s.payload) as $field(u_context_t::uds) $(s.payload.uds);
    rewrite each $(h) as PL_Engine (PL_Engine?._0 $(h));
  }
  
  ghost fn elim_context_full_pred_cdi ($(s): $type(context_t)) (#$(h): context_full_data)
    requires with_pure ($(tag_relation(s, h)) /\ PL_L0? $(h))
    requires $(context_full_pred(s, h))
    ensures cdi_pred $(s.payload.cdi) (PL_L0?._0 $(h))
  {
    unfold Let_context_full_pred.func_context_full_pred _ _;
    rewrite each $(s.payload) as $field(u_context_t::cdi) $(s.payload.cdi);
    rewrite each $(h) as PL_L0 (PL_L0?._0 $(h));
  }
  
  ghost fn elim_context_full_pred_l1 ($(s): $type(context_t)) (#$(h): context_full_data)
    requires with_pure ($(tag_relation(s, h)) /\ PL_L1? $(h))
    requires $(context_full_pred(s, h))
  {
    unfold Let_context_full_pred.func_context_full_pred _ _;
    rewrite each $(s.payload) as $field(u_context_t::l1_context) $(s.payload.l1_context);
    rewrite each $(h) as PL_L1;
  }

  ghost fn intro_context_full_pred_uds ($(s): $type(context_t)) #uds
    requires with_pure $(tag_relation(s, _inline_pulse(PL_Engine uds)))
    requires uds_pred $(s.payload.uds) uds
    ensures $(context_full_pred(s, _inline_pulse(PL_Engine uds)))
  {
    rewrite uds_pred $(s.payload.uds) uds
      as $(context_full_pred(s, _inline_pulse(PL_Engine uds)));
  }

  ghost fn intro_context_full_pred_cdi ($(s): $type(context_t)) #cdi
    requires with_pure $(tag_relation(s, _inline_pulse(PL_L0 cdi)))
    requires cdi_pred $(s.payload.cdi) cdi
    ensures $(context_full_pred(s, _inline_pulse(PL_L0 cdi)))
  {
    rewrite cdi_pred $(s.payload.cdi) cdi
      as $(context_full_pred(s, _inline_pulse(PL_L0 cdi)));
  }
)

void memcpy_(size_t len, _array const uint8_t *a1, _out _array uint8_t *a2)
  _preserves(a1._length == len)
  _preserves(a2._length == len)
  _ensures((bool) _inline_pulse(array_value_of $(a2) == array_value_of $(a1)))
{
  _ghost_stmt(admit());
}

_refine_value(context_full_data state,
  tag_relation(*this, _inline_pulse(state)) && context_full_pred(*this, _inline_pulse(state)))
typedef context_t *context_obj;

_letimpure(context_full_data engine_state(const context_obj ctx),
  _inline_pulse(observe (fun h -> $(context_full_pred(*ctx, _inline_pulse(h))))))

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

_let(bool is_pl_engine(context_full_data state), _inline_pulse(DPE_context_full_data.PL_Engine? $(state)))
_let(bool is_pl_l0(context_full_data state), _inline_pulse(DPE_context_full_data.PL_L0? $(state)))

void init_l0_context(context_obj ctx, const dice_digest cdi)
  _requires(is_pl_engine(engine_state(ctx)))
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
  _ensures(return ==> is_pl_l0(engine_state(ctx)))
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