
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

/* parameters: 1 <= w <= 14; n = 2^w */
/* input: permutation pi of {0,1,...,n-1} */
/* output: (2m-1)n/2 control bits at positions pos,pos+step,... */
/* output position pos is by definition 1&(out[pos/8]>>(pos&7)) */
/* caller must 0-initialize positions first */
/* temp must have space for int32[2*n] */
static void cbf(bool* bit, bool* put2, int16_t* q, const int16_t *pi, int w) {
    const int n = 1 << w;
    const int step = 1 << (GFBITS - w);

    for (int x = 0; x < n; ++x) {
        assert(0 <= pi[x] && pi[x] < n);
    }

    int16_t pi_inv[n];
    memset(pi_inv, -1, sizeof(int16_t) * n);
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
    /* B = (p<<16)+c */

    if (w <= 10) {
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
    } else {
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

    int16_t C[n];
    for (int k = 0; k < n; ++k) {
        C[k] = bit[pi[k]/2] ? pi[k]^1 : pi[k];
    }

    for (int k = 0; k < n/2; ++k) {
        put2[k] = (C[2*k]&1) == 1; /* l[k] */
    }

    for (int j = 0; j < n/2; ++j) {
        q[j]     = C[2*j + (C[2*j]&1 ? 1 : 0)] >> 1;
    }
    for (int j = 0; j < n/2; ++j) {
        q[j+n/2] = C[2*j + (C[2*j]&1 ? 0 : 1)] >> 1;
    }
}


/* parameters: 1 <= w <= 14; n = 2^w */
/* input: permutation pi of {0,1,...,n-1} */
/* output: (2m-1)n/2 control bits at positions pos,pos+step,... */
/* output position pos is by definition 1&(out[pos/8]>>(pos&7)) */
/* caller must 0-initialize positions first */
/* temp must have space for int32[2*n] */
static void cbrecursion(bool* out2, const int16_t *pi, int w) {
    assert(w >= 1);
    if (w == 1) {
        int pos = (1 << (GFBITS - 1)) * (GFBITS - 1);
        assert(!out2[pos]);
        assert((pi[0] & ~1) == 0);
        out2[pos] = (pi[0] & 1);
        return;
    }

    const int n = 1 << w;
    int wk = GFBITS - w;

    const int step = 1 << wk;
    assert(step <= (1 << (GFBITS - 2)));

    // B refers to the second n elements in temp.
    int16_t q[n];

    bool bit[n/2];
    bool put2[n/2];
    cbf(bit, put2, q, pi, w);

    cbrecursion(out2,      q,     w-1);
    cbrecursion(out2+step, q+n/2, w-1);

    for (int j = 0; j < n/2; ++j) {
        int32_t fj = bit[j] ? 1 : 0;

        int pos2 = step * (1 << (w-1)) * (GFBITS - w) + step * j;

        assert(!out2[pos2]);
        out2[pos2] = bit[j];
    }
    for (int j = 0; j < n/2; ++j) {
        int pos2 = step * (1 << (w-1)) * (GFBITS + w - 2) + step * j;
        assert(!out2[pos2]);
        out2[pos2] = put2[j];
    }
}

extern "C" lean_obj_res lean_controlbitsfrompermutation2(b_lean_obj_arg pi_obj) {
    const size_t perm_count = 1 << GFBITS;
    assert(lean_array_size(pi_obj) == perm_count);
    gf pi[perm_count];
    init_gf_array(pi, pi_obj);

    const size_t cond_bytes = (1 << 8) * 23;

    const size_t cnt = (1 << (GFBITS - 1)) * (2*GFBITS-1);
    bool out2[cnt];
    memset(out2, 0, sizeof(out2));

    cbrecursion(out2, (int16_t*)pi, GFBITS);

    lean_obj_res out_obj = lean_alloc_sarray1(1, cond_bytes);
    uint8_t* out = lean_sarray_cptr(out_obj);
    for (int i = 0; i != cnt >> 3; ++i) {
        uint8_t r = 0;
        for (int j = 0; j != 8; ++j) {
            r |= out2[8*i+j] ? (1 << j) : 0;
        }
        out[i] = r;
    }

    return out_obj;
}