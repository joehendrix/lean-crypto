
#define CRYPTO_NAMESPACE(x) x

#include <lean/lean.h>
#include <stdlib.h>
#include <string.h>
extern "C" {
#include "nist/rng.h"
}
extern "C" {
#include "crypto_kem.h"
#include "operations.h"

#include "controlbits.h"
#include "randombytes.h"
#include "crypto_hash.h"
#include "encrypt.h"
#include "decrypt.h"
#include "params.h"
#include "sk_gen.h"
#include "pk_gen.h"
#include "util.h"

}

namespace lean {
    lean_obj_res io_wrap_handle(FILE * hfile);
}

/**
 * @brief Open a stream using a file descriptor.
 * 
 * @param fd 
 * @return Handle
 */
extern "C" LEAN_EXPORT lean_obj_res open_fd_write(uint32_t fd) {
    FILE* fp = fdopen(fd, "w");
    if (!fp) {
        return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("FILE_OPEN_ERROR Lean")));
    }
    return lean_io_result_mk_ok(lean::io_wrap_handle(fp));
}

extern "C" uint8_t lean_byte_array_decide_eq(b_lean_obj_arg x, b_lean_obj_arg y) {
    size_t n = lean_sarray_size(x);
    if (n != lean_sarray_size(y)) {
        return 0;
    }
    if (memcmp(lean_sarray_cptr(x), lean_sarray_cptr(y), n)) {
        return 0;
    } 
    return 1;
}

static inline
lean_obj_res lean_alloc_sarray1(unsigned elem_size, size_t size) {
    return lean_alloc_sarray(elem_size, size, size);
}

extern "C" lean_obj_res lean_randombytes_init(b_lean_obj_arg entropy_input_array, b_lean_obj_arg _rw) {
    if (lean_sarray_size(entropy_input_array) != 48) {
        return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("INIT_FAILURE")));

    }
    unsigned char* entropy_input = lean_sarray_cptr(entropy_input_array);
    randombytes_init(entropy_input, NULL, 256);
    return lean_io_result_mk_ok(lean_box(0));
}

// lean_obj_arg scratch,
extern "C" lean_obj_res lean_randombytes(b_lean_obj_arg size, b_lean_obj_arg _rw) {
    if (LEAN_UNLIKELY(!lean_is_scalar(size))) {
        lean_internal_panic_out_of_memory();
    }

    size_t n = lean_unbox(size);
    lean_obj_res r = lean_alloc_sarray1(1, n);
    uint8_t* seed = lean_sarray_cptr(r);        
    randombytes(seed, n);
    return lean_io_result_mk_ok(r);
}

inline static lean_obj_res lean_mk_pair(lean_obj_arg x, lean_obj_arg y) {
    lean_object * r = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(r, 0, x);
    lean_ctor_set(r, 1, y);
    return r;
}

inline static lean_obj_res lean_mk_keypair(lean_obj_arg pk, lean_obj_arg sk) {
    return lean_mk_pair(pk, sk);
}

inline static lean_obj_res lean_mk_option_none(void) {
    return lean_alloc_ctor(0, 0, 0);
}

inline static lean_obj_res lean_mk_option_some(lean_obj_arg v) {
    lean_object * r = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(r, 0, v);
    return r;
}

extern "C" lean_obj_res lean_try_crypto_kem_keypair(lean_obj_arg seed_in_obj) {

    int i;
    unsigned char r[ SYS_N/8 + (1 << GFBITS)*sizeof(uint32_t) + SYS_T*2 + 32 ];
    unsigned char *rp;

    lean_obj_res pk_array = lean_alloc_sarray1(1, crypto_kem_PUBLICKEYBYTES);        
    uint8_t* pk = lean_sarray_cptr(pk_array);        

    lean_obj_res sk_array = lean_alloc_sarray1(1, crypto_kem_SECRETKEYBYTES);        
    uint8_t* sk = lean_sarray_cptr(sk_array);        

    gf f[ SYS_T ]; // element in GF(2^mt)
    gf irr[ SYS_T ]; // Goppa polynomial
    uint32_t perm[ 1 << GFBITS ]; // random permutation as 32-bit integers
    int16_t pi[ 1 << GFBITS ]; // random permutation
    rp = &r[ sizeof(r)-32 ];
    unsigned char *skp = sk;

    unsigned char* seed_in = lean_sarray_cptr(seed_in_obj);

    // expanding and updating the seed
    shake(r, sizeof(r), seed_in, 33);
    memcpy(skp, seed_in+1, 32);
    skp += 32 + 8;

    // Update the seed
    lean_obj_res seed_out_obj;
    unsigned char* seed_out;
    if (lean_is_exclusive(seed_in_obj)) {
        seed_out_obj = seed_in_obj;
        seed_out = seed_in;
    } else {
        seed_out_obj = lean_alloc_sarray1(1, 33);
        seed_out = lean_sarray_cptr(seed_out_obj);
        seed_out[0] = seed_in[0];
        lean_dec_ref(seed_in_obj);
    }
    memcpy(seed_out+1, &r[ sizeof(r)-32 ], 32);


    // generating irreducible polynomial

    rp -= sizeof(f); 

    for (i = 0; i < SYS_T; i++) 
        f[i] = load_gf(rp + i*2); 

    if (genpoly_gen(irr, f)) {
        return lean_mk_pair(lean_mk_option_none(), seed_out_obj);
    } 

    for (i = 0; i < SYS_T; i++)
        store_gf(skp + i*2, irr[i]);

    skp += IRR_BYTES;

    // generating permutation

    rp -= sizeof(perm);

    for (i = 0; i < (1 << GFBITS); i++) 
        perm[i] = load4(rp + i*4); 

    if (pk_gen(pk, skp - IRR_BYTES, perm, pi)) {
        return lean_mk_pair(lean_mk_option_none(), seed_out_obj);
    }

    controlbitsfrompermutation(skp, pi, GFBITS, 1 << GFBITS);
    skp += COND_BYTES;

    // storing the random string s

    rp -= SYS_N/8;
    memcpy(skp, rp, SYS_N/8);

    // storing positions of the 32 pivots
    store8(sk + 32, 0xFFFFFFFF);
    
    return lean_mk_pair(lean_mk_option_some(lean_mk_keypair(pk_array, sk_array)), seed_out_obj);
}

extern "C" lean_obj_res lean_crypto_enc(b_lean_obj_arg pk_array, b_lean_obj_arg _rw) {
    uint8_t* pk = lean_sarray_cptr(pk_array);        

    lean_obj_res c_array = lean_alloc_sarray1(1, SYND_BYTES);        
    uint8_t* c = lean_sarray_cptr(c_array);        

    lean_obj_res e_array = lean_alloc_sarray1(1, SYS_N/8);        
    uint8_t* e = lean_sarray_cptr(e_array);        

	encrypt(c, pk, e);

    return lean_io_result_mk_ok(lean_mk_pair(c_array, e_array));
} 

extern "C" lean_obj_res lean_crypto_hash_32b(b_lean_obj_arg input) {
    lean_obj_res key_array = lean_alloc_sarray1(1, crypto_kem_BYTES);        
    uint8_t* key = lean_sarray_cptr(key_array);        

	crypto_hash_32b(key, lean_sarray_cptr(input), lean_sarray_size(input));
    
    return key_array;
}

extern "C" lean_obj_res lean_decrypt(b_lean_obj_arg ct_array, b_lean_obj_arg sk_array) {
    uint8_t* sk = lean_sarray_cptr(sk_array);        
    uint8_t* c = lean_sarray_cptr(ct_array);        
    lean_obj_res e_array = lean_alloc_sarray1(1, SYS_N/8);        
    uint8_t* e = lean_sarray_cptr(e_array);        

	unsigned char ret_decrypt = decrypt(e, sk, c);
    
    lean_object * r = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(r, 0, e_array);
    lean_ctor_set(r, 1, lean_box(ret_decrypt));
    return r;
}