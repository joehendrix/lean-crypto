#include <lean/lean.h>
#include <stdlib.h>
#include <string.h>
extern "C" {
#include "nist/rng.h"
}
extern "C" {
#include "crypto_kem.h"
}

#define KAT_SUCCESS          0
#define KAT_FILE_OPEN_ERROR -1
#define KAT_CRYPTO_FAILURE  -4
#define KATNUM 10

extern "C" void fprintBstr(FILE *fp, const char *S, unsigned char *A, unsigned long long L);

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

extern "C" lean_obj_res lean_bytearray_decide_eq(b_lean_obj_arg x, b_lean_obj_arg y) {

    size_t n = lean_sarray_size(x);
    if (n != lean_sarray_size(y)) {
        return lean_alloc_ctor(1, 0, 0);
    }

    uint8_t* xp = lean_sarray_cptr(x);        
    uint8_t* yp = lean_sarray_cptr(y); 
    if (memcmp(lean_sarray_cptr(y), lean_sarray_cptr(y), n)) {
        return lean_alloc_ctor(1, 0, 0);

    } 

    return lean_alloc_ctor(2, 0, 0);
}

static inline
lean_obj_res lean_alloc_sarray1(unsigned elem_size, size_t size) {
    return lean_alloc_sarray(elem_size, size, size);
}

extern "C" lean_obj_res init_seed(b_lean_obj_arg arg) {
    //lean_dec_ref(arg);

    lean_obj_res a = lean_alloc_array(KATNUM, KATNUM);
    lean_object** aptr = lean_array_cptr(a);
    
    unsigned char entropy_input[48];
    for (int i=0; i<48; i++)
        entropy_input[i] = i;
    randombytes_init(entropy_input, NULL, 256);

    unsigned char seed[KATNUM][48];
    for (int i=0; i<KATNUM; i++) {
        lean_obj_res byte_array = lean_alloc_sarray1(1, 48);        
        uint8_t* seed = lean_sarray_cptr(byte_array);        
        randombytes(seed, 48);
        aptr[i] = byte_array;
    }
    return a;
}

extern "C" lean_obj_res lean_crypto_kem_keypair(b_lean_obj_arg seed_array) {
    uint8_t* seed = lean_sarray_cptr(seed_array);        

    lean_obj_res pk_array = lean_alloc_sarray1(1, crypto_kem_PUBLICKEYBYTES);        
    uint8_t* pk = lean_sarray_cptr(pk_array);        

    lean_obj_res sk_array = lean_alloc_sarray1(1, crypto_kem_SECRETKEYBYTES);        
    uint8_t* sk = lean_sarray_cptr(sk_array);        

    int ret_val;
    randombytes_init(seed, NULL, 256);
    if ( (ret_val = crypto_kem_keypair(pk, sk)) != 0) {
        fprintf(stderr, "crypto_kem_keypair returned <%d>\n", ret_val);
        return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("CRYPTO_FAILURE")));
    }

    lean_object * r = lean_alloc_ctor(1, 2, 0);
    lean_ctor_set(r, 0, pk_array);
    lean_ctor_set(r, 1, sk_array);
    return lean_io_result_mk_ok(r);
}

extern "C" lean_obj_res lean_crypto_kem_enc(b_lean_obj_arg pk_array) {
    uint8_t* pk = lean_sarray_cptr(pk_array);        

    lean_obj_res ss_array = lean_alloc_sarray1(1, crypto_kem_BYTES);        
    uint8_t* ss = lean_sarray_cptr(ss_array);        

    lean_obj_res ct_array = lean_alloc_sarray1(1, crypto_kem_CIPHERTEXTBYTES);        
    uint8_t* ct = lean_sarray_cptr(ct_array);        

    int ret_val;
    if ( (ret_val = crypto_kem_enc(ct, ss, pk)) != 0) {
        fprintf(stderr, "crypto_kem_enc returned <%d>\n", ret_val);
        return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("CRYPTO_FAILURE")));
    }

    lean_object * r = lean_alloc_ctor(1, 2, 0);
    lean_ctor_set(r, 0, ss_array);
    lean_ctor_set(r, 1, ct_array);
    return lean_io_result_mk_ok(r);
}

extern "C" lean_obj_res lean_crypto_kem_dec(b_lean_obj_arg ct_array, b_lean_obj_arg sk_array) {
    uint8_t* ct = lean_sarray_cptr(ct_array);        
    uint8_t* sk = lean_sarray_cptr(sk_array);        

    lean_obj_res ss1_array = lean_alloc_sarray1(1, crypto_kem_BYTES);        
    uint8_t* ss1 = lean_sarray_cptr(ss1_array);        
    int ret_val;
    if ( (ret_val = crypto_kem_dec(ss1, ct, sk)) != 0) {
        fprintf(stderr, "crypto_kem_dec returned <%d>\n", ret_val);
        return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("CRYPTO_FAILURE")));
    }

    return lean_io_result_mk_ok(ss1_array);
}