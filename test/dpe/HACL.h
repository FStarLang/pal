#ifndef _HACL_H_
#define _HACL_H_
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>
#include "pal.h"

typedef uint8_t *ed25519_key
    _refine(this._length == 32) _array;
typedef uint8_t *ed25519_sig
    _refine(this._length == 64) _array;

bool ed25519_verify(const ed25519_key pubk, const _array uint8_t *hdr, size_t hdr_len, const ed25519_sig sig)
    _requires(hdr._length == hdr_len);

#define DICE_DIGEST_LEN 64 //TODO generalize
_refine(this._length == DICE_DIGEST_LEN) _array
typedef uint8_t *dice_digest;

void hacl_hash(uint8_t alg, size_t src_len, const _array uint8_t *src, _out dice_digest dst)
    _requires(src._length == src_len);


void hacl_hmac(uint8_t alg, _out dice_digest dst,
    const _array uint8_t *key, size_t key_len,
    const _array uint8_t *msg, size_t msg_len)
    _requires(key._length == key_len)
    _requires(msg._length == msg_len);

size_t hashf(uint16_t key);
#endif