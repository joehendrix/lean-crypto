
#define CRYPTO_NAMESPACE(x) x
#include <lean/lean.h>
#include <stdlib.h>
#include <string.h>
extern "C" {
#include "crypto_hash.h"
#include "gf.h"
#include "params.h"
#include "util.h"
}
#include <gmp.h>

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

static void init_gf_array(gf* s, b_lean_obj_arg obj) {
    for (size_t i = 0; i != lean_array_size(obj); ++i) {
        s[i] = lean_unbox_uint32(lean_array_get_core(obj, i));
    }
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


# define AES_MAXNR 14

/* This should be a hidden type, but EVP requires that the size be known */
struct aes_key_st {
    unsigned int rd_key[4 * (AES_MAXNR + 1)];
    int rounds;
};

typedef struct aes_key_st AES_KEY;

extern "C"
int AES_set_encrypt_key(const unsigned char *userKey, const int bits,
                        AES_KEY *key);

extern "C"
void AES_encrypt(const unsigned char *in, unsigned char *out,
                 const AES_KEY *key);

extern "C" lean_obj_res lean_AES256_ECB(b_lean_obj_arg key_obj, b_lean_obj_arg v_obj) {
    assert(lean_sarray_size(key_obj) == 32);
    const uint8_t* key = lean_sarray_cptr(key_obj);

    assert(lean_sarray_size(v_obj) == 16);
    const uint8_t* ctr = lean_sarray_cptr(v_obj);

    lean_obj_res buffer_obj = lean_alloc_sarray1(1, 16);
    uint8_t* buffer = lean_sarray_cptr(buffer_obj);
    assert(key);

    AES_KEY ks;
    memset(&ks, 0, sizeof(AES_KEY));
    int ret = AES_set_encrypt_key(key, 256, &ks);
    assert(ret >= 0);
    AES_encrypt(ctr, buffer, &ks);

    return buffer_obj;
}

extern "C" lean_obj_res lean_shake256(b_lean_obj_arg size_obj, b_lean_obj_arg in_obj) {
    if (LEAN_UNLIKELY(!lean_is_scalar(size_obj))) {
        lean_internal_panic_out_of_memory();
    }
    size_t size = lean_unbox(size_obj);
    lean_obj_res r_obj = lean_alloc_sarray1(1, size);

    shake(lean_sarray_cptr(r_obj), size, lean_sarray_cptr(in_obj), lean_sarray_size(in_obj));

    return r_obj;
}

/* parameters: 1 <= w <= 10; n = 2^w */
/* input: permutation pi of {0,1,...,n-1} */
/* output: (2m-1)n/2 control bits at positions pos,pos+step,... */
/* output position pos is by definition 1&(out[pos/8]>>(pos&7)) */
/* caller must 0-initialize positions first */
/* temp must have space for int32[2*n] */
static void cbf_le(bool* bit, const int16_t *pi, const int16_t* pi_inv, const int16_t* E, const int16_t* E_min, int w) {
    const int n = 1 << w;
    assert(w <= 10);


    int16_t B00[n];
    int16_t B10[n];
    for (int x = 0; x < n; ++x) {
        B00[x] = E_min[x];
        B10[x] = E[E[x]];
    }

    for (int i = 1; i < w-1; ++i) {
        /* B = (p<<10)+c */

        int16_t B00_copy[n];
        for (int x = 0;x < n;++x)
            B00_copy[x] = B00[x]; /* A = (p^{-1}<<20)+(p<<10)+c */
        for (int x = 0; x < n; ++x) {
            if (B00_copy[B10[x]] < B00_copy[x]) {
                B00[x] = B00_copy[B10[x]];
            } else {
                B00[x] = B00_copy[x];
            }
        }

        int16_t B10_copy[n];
        for (int x = 0;x < n;++x)
            B10_copy[x] = B10[x]; /* A = (p^{-1}<<20)+(p<<10)+c */
        for (int x = 0; x < n; ++x)
            B10[x] = B10_copy[B10_copy[x]];
    }
    for (int x = 0; x < n/2; ++x)
        bit[x] = B00[2*x] & 1;
}

/* parameters: 1 <= w <= 14; n = 2^w */
/* input: permutation pi of {0,1,...,n-1} */
/* output: (2m-1)n/2 control bits at positions pos,pos+step,... */
/* output position pos is by definition 1&(out[pos/8]>>(pos&7)) */
/* caller must 0-initialize positions first */
/* temp must have space for int32[2*n] */
static void cbf_gt(bool* bit, const int16_t *pi, const int16_t* pi_inv, const int16_t* E, const int16_t* E_min, int w) {
    const int n = 1 << w;
    assert(w > 10);

    int16_t B00[n];
    int16_t B16[n];

    for (int x = 0;x < n;++x) {
        B00[x] = E_min[x];
        B16[x] = E[E[x]];
    }

    for (int i = 1;i < w-1;++i) {
        /* B = (p<<16)+c */

        int32_t A[n];
        for (int x = 0;x < n;++x)
            A[x] = B00[B16[x]];
        /* A = p^(-1)<<16+c */

        if (i < w-2) {
            int32_t H[n];
            for (int x = 0;x < n;++x)
                H[x] = B16[B16[x]];
            for (int x = 0; x < n; ++x)
                B16[x] = H[x];
            /* B = (p^(-2)<<16)+c */
        }

        /* A = id<<16+cp */
        for (long long x = 0;x < n;++x) {
            if (A[x] < B00[x]) {
                B00[x] = A[x];
            }
        }
    }

    for (int x = 0; x < n/2; ++x)
        bit[x] = B00[2*x] & 0x1;
}

extern "C"
lean_obj_res
lean_cbf(b_lean_obj_arg off_obj, b_lean_obj_arg w_obj, b_lean_obj_arg pi_obj) {
    const int row_size = 1 << (GFBITS - 1);
    const size_t cnt = row_size * (2*GFBITS-1);
    assert(lean_is_scalar(off_obj));
    size_t off = lean_unbox(off_obj);
    size_t w = lean_unbox(w_obj) + 1;
    assert(w > 1);
    const int n = 1 << w;
    const size_t perm_count = n;
    assert(lean_array_size(pi_obj) == perm_count);
    gf pi[perm_count];
    init_gf_array(pi, pi_obj);

    uint16_t pi_inv[n];
    memset(pi_inv, -1, sizeof(uint16_t) * n);
    for (int x = 0; x < n; ++x)
        pi_inv[pi[x]] = x;
    for (int16_t x = 0; x < n; ++x) {
        assert(0 <= pi_inv[x] && pi_inv[x] < n);
    }

    int16_t E[n];
    memset(E, -1, sizeof(int16_t) * n);
    for (int x = 0; x < n; ++x)
        E[x] = pi[pi_inv[x^1]^1];

    int16_t E_min[n];
    for (int x = 0; x < n; ++x) {
        E_min[x] = (x < E[x]) ? x : E[x];
    }

    bool bit[1 << lean_unbox(w_obj)];
    if (w <= 10) {
        cbf_le(bit, (int16_t*) pi, (int16_t*) pi_inv, E, E_min, w);
    } else {
        cbf_gt(bit, (int16_t*) pi, (int16_t*) pi_inv, E, E_min, w);
    }

    lean_obj_res bit_obj = lean_alloc_array(n/2, n/2);
    lean_object** out = lean_array_cptr(bit_obj);
    for (int j = 0; j < n/2; ++j) {
        out[j] = lean_box(bit[j] ? 1 : 0);
    }
    return bit_obj;
}