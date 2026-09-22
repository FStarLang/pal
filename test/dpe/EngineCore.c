#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>
#include "pal.h"
#include "DPE.h"
#include "EngineCore.h"
#include "HACL.h"

#ifdef PALOW
// Palow: the old model reads an array's value off the array object with
// `array_value_of`, but a Palow array pointer is just an address, so the value
// is a binder in the contract. `_plain` is what says the ownership is spelled
// by hand here rather than granted automatically.
bool compare(size_t len, _plain const _array uint8_t *a1, _plain const _array uint8_t *a2)
    _preserves(_inline_pulse(array_pts_to uint8_t_repr 1 $(a1) $`p_a1 $`v_a1))
    _preserves(_inline_pulse(array_pts_to uint8_t_repr 1 $(a2) $`p_a2 $`v_a2))
    _requires((bool) _inline_pulse(Seq.length $`v_a1 == SizeT.v $(len)))
    _requires((bool) _inline_pulse(Seq.length $`v_a2 == SizeT.v $(len)))
    _ensures(return == (bool) _inline_pulse(Seq.equal $`v_a1 $`v_a2))
#else
bool compare(size_t len, const _array uint8_t *a1, const _array uint8_t *a2)
    _requires(a1._length == len)
    _requires(a2._length == len)
    _ensures(return == (bool) _inline_pulse(Seq.equal (array_value_of $(a1)) (array_value_of $(a2))))
#endif

{
    _ghost_stmt(admit());
    return false;
}

bool authenticate_l0_image(const engine_record_t *record)
{
    bool valid_header_sig = ed25519_verify(record->l0_image_auth_pubkey, record->l0_image_header, record->l0_image_header_size, record->l0_image_header_sig);
    if (valid_header_sig)
    {   
        uint8_t scratch[DICE_DIGEST_LEN];
        //allocate a scratch of size DICE_HASH_ALG here and use it
        hacl_hash(DICE_HASH_ALG, record->l0_binary_size, record->l0_binary, scratch);
        return compare(DICE_DIGEST_LEN, scratch, record->l0_binary_hash);
    }
    else
    {
        return false;
    }
}

void compute_cdi(_out dice_digest cdi, const uds_array uds, const engine_record_t *record) {
    uint8_t uds_digest[DICE_DIGEST_LEN];
    uint8_t l0_digest[DICE_DIGEST_LEN];
    hacl_hash(DICE_HASH_ALG, UDS_LEN, uds, uds_digest);
    hacl_hash(DICE_HASH_ALG, record->l0_binary_size, record->l0_binary, l0_digest);
    hacl_hmac(DICE_HASH_ALG, cdi, uds_digest, DICE_DIGEST_LEN, l0_digest, DICE_DIGEST_LEN);
}

bool engine_main(dice_digest cdi, const uds_array uds, const engine_record_t *record) {
    if (authenticate_l0_image(record)) {
        compute_cdi(cdi, uds, record);
        return true;
    } else {
        return false;
    }
}