#ifndef _DPE_H_
#define _DPE_H_

#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>
#include "pal.h"
#include "HACL.h"

#define _allocated_array _refine((_slprop) _inline_pulse(freeable_array $(this)))

#define UDS_LEN 32
_refine(this._length == UDS_LEN) _array
typedef uint8_t *uds_array;


#define DICE_SUCCESS 0
#define DICE_ERROR 1
#define SHA2_256 0 //maybe use an enum for this?
#define DICE_HASH_ALG SHA2_256 

_refine(this.l0_image_header._length == this.l0_image_header_size)
_refine(this.l0_binary._length == this.l0_binary_size)
typedef struct _pulse_eager_unfold_predicate _engine_record_t {
    size_t  l0_image_header_size;
    _array uint8_t *l0_image_header;
    ed25519_sig l0_image_header_sig;
    size_t  l0_binary_size;
    _array uint8_t *l0_binary;
    dice_digest l0_binary_hash;
    ed25519_key l0_image_auth_pubkey;
} engine_record_t;

_refine(this.deviceIDCSR._length == this.deviceIDCSR_len)
_refine(this.aliasKeyCRT._length == this.aliasKeyCRT_len)
typedef struct _pulse_eager_unfold_predicate {
  ed25519_key deviceID_pub;
  ed25519_key aliasKey_priv;
  ed25519_key aliasKey_pub;
  size_t deviceIDCSR_len;
  _array uint8_t *deviceIDCSR;
  size_t aliasKeyCRT_len;
  _array uint8_t *aliasKeyCRT;
} l1_context_t;

#define ENGINE_CONTEXT 0
#define L0_CONTEXT 1
#define L1_CONTEXT 2

typedef union _u_context_t {
  _allocated uds_array uds;
  _allocated dice_digest cdi;
  l1_context_t l1_context;
} u_context_t;

typedef struct {
  uint8_t tag;
  u_context_t payload;
} context_t;
#endif