
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

extern "C" LEAN_EXPORT lean_object * lean_alloc_mpz(mpz_t v);
extern "C" LEAN_EXPORT void lean_extract_mpz_value(lean_object * o, mpz_t v);

static lean_obj_res nat_import_from_bytes(size_t n, const unsigned char* a) {
    if (n == 0)
        return lean_box(0);
    mpz_t r;
    mpz_init2(r, 8*n);
    mpz_import(r, n, 1, 1, -1, 0, a);

    if (mpz_cmp_ui(r, LEAN_MAX_SMALL_NAT) <= 0) {
        lean_obj_res o = lean_box(mpz_get_ui(r));
        mpz_clear(r);
        return o;
    }
    return lean_alloc_mpz(r);
}

static void nat_export_to_bytes(size_t n, unsigned char* a, b_lean_obj_arg x) {
    if (n == 0)
        return;
    mpz_t xz;
    if (lean_is_scalar(x)) {
        mpz_init_set_ui(xz, lean_unbox(x));
    } else {
        mpz_init(xz);
        lean_extract_mpz_value(x, xz);
    }

    size_t count;
    mpz_export(a, &count, 1, 1, -1, 0, xz);
    assert(count <= n);
    if (count < n) {
        memmove(a + (n-count), a, count);
        memset(a, 0, n-count);
    }
    // Set remaining bits
    mpz_clear(xz);
}

static void nat_export_to_bytes_lsb(size_t n, unsigned char* a, b_lean_obj_arg x) {
    if (n == 0)
        return;
    mpz_t xz;
    if (lean_is_scalar(x)) {
        mpz_init_set_ui(xz, lean_unbox(x));
    } else {
        mpz_init(xz);
        lean_extract_mpz_value(x, xz);
    }

    size_t count;
    mpz_export(a, &count, -1, 1, -1, 0, xz);
    assert(count <= n);
    if (count < n) {
        memmove(a + (n-count), a, count);
        memset(a, 0, n-count);
    }
    // Set remaining bits
    mpz_clear(xz);
}

# define AES_MAXNR 14

/* This should be a hidden type, but EVP requires that the size be known */
struct aes_key_st {
    unsigned int rd_key[4 * (AES_MAXNR + 1)];
    int rounds;
};

typedef struct aes_key_st AES_KEY;

extern "C" {
int aesni_set_encrypt_key(const unsigned char *userKey, int bits, AES_KEY *key);

void aesni_ecb_encrypt(const unsigned char *in,
                       unsigned char *out,
                       size_t length, const AES_KEY *key, int enc);

int AES_set_encrypt_key(const unsigned char *userKey, const int bits,
                        AES_KEY *key);

void AES_ecb_encrypt(const unsigned char *in, unsigned char *out,
                     const AES_KEY *key, const int enc);

}

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

inline static lean_obj_res lean_mk_option_none(void) {
    return lean_alloc_ctor(0, 0, 0);
}

inline static lean_obj_res lean_mk_option_some(lean_obj_arg v) {
    lean_object * r = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(r, 0, v);
    return r;
}

inline static lean_obj_res lean_mk_pair(b_lean_obj_arg x, b_lean_obj_arg y) {
    lean_object * r = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(r, 0, x);
    lean_ctor_set(r, 0, y);
    return r;
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

extern "C" lean_obj_res lean_store_gf(b_lean_obj_arg irr_obj) {
    assert(lean_array_size(irr_obj) == SYS_T);
    gf irr[SYS_T];
    init_gf_array(irr, irr_obj);

    lean_obj_res sk_obj = lean_alloc_sarray1(1, 2 * SYS_T);
    uint8_t* sk = lean_sarray_cptr(sk_obj);

    // generating irreducible polynomial
    for (size_t i = 0; i < SYS_T; i++)
        store_gf(sk + i*2, irr[i]);

    return sk_obj;
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

/* input: in, a 64x64 matrix over GF(2) */
/* output: out, transpose of in */
static
void my_transpose_64x64(uint64_t * out, uint64_t * in)
{
	int i, j, s, d;

	uint64_t x, y;
	uint64_t masks[6][2] = {
	                        {0x5555555555555555, 0xAAAAAAAAAAAAAAAA},
	                        {0x3333333333333333, 0xCCCCCCCCCCCCCCCC},
	                        {0x0F0F0F0F0F0F0F0F, 0xF0F0F0F0F0F0F0F0},
	                        {0x00FF00FF00FF00FF, 0xFF00FF00FF00FF00},
	                        {0x0000FFFF0000FFFF, 0xFFFF0000FFFF0000},
	                        {0x00000000FFFFFFFF, 0xFFFFFFFF00000000}
	                       };

	for (i = 0; i < 64; i++)
		out[i] = in[i];

	for (d = 5; d >= 0; d--)
	{
		s = 1 << d;

		for (i = 0; i < 64; i += s*2)
		for (j = i; j < i+s; j++)
		{
			x = (out[j] & masks[d][0]) | ((out[j+s] & masks[d][0]) << s);
			y = ((out[j] & masks[d][1]) >> s) | (out[j+s] & masks[d][1]);

			out[j+0] = x;
			out[j+s] = y;
		}
	}
}

extern "C" lean_obj_res lean_transpose64(b_lean_obj_arg a_obj) {
    assert(lean_array_size(a_obj) == 64);
	uint64_t bs[64];
	for (int i = 0; i < 64; i++) {
        bs[i] = lean_unbox_uint64(lean_array_get_core(a_obj, i));
	}

	my_transpose_64x64(bs, bs);

    lean_obj_res r_obj = lean_alloc_array(64, 64);
	for (int i = 0; i < 64; i++) {
        lean_array_set_core(r_obj, i, lean_box_uint64(bs[i]));
	}
    return r_obj;
}

extern "C" lean_obj_res lean_elt_from_bytevec(b_lean_obj_arg w_obj, b_lean_obj_arg r_obj, b_lean_obj_arg x_obj) {
    if (LEAN_UNLIKELY(!lean_is_scalar(w_obj))) {
        lean_internal_panic_out_of_memory();
    }
    size_t w = lean_unbox(w_obj);

    if (LEAN_UNLIKELY(!lean_is_scalar(r_obj))) {
        lean_internal_panic_out_of_memory();
    }
    size_t r = lean_unbox(r_obj);
    assert(r == 8*w);

    assert(lean_sarray_size(x_obj) == w);
    const uint8_t* x = lean_sarray_cptr(x_obj);

    return nat_import_from_bytes(w, x);
}

extern "C" lean_obj_res lean_elt_to_bytevec(b_lean_obj_arg r_obj, b_lean_obj_arg w_obj, b_lean_obj_arg x) {
    if (LEAN_UNLIKELY(!lean_is_scalar(w_obj))) {
        lean_internal_panic_out_of_memory();
    }
    size_t w = lean_unbox(w_obj);

    lean_obj_res e_obj = lean_alloc_sarray1(1, w);
    nat_export_to_bytes(w, lean_sarray_cptr(e_obj), x);
    return e_obj;
}

extern "C" lean_obj_res lean_nat_to_bytevec_lsb(b_lean_obj_arg r_obj, b_lean_obj_arg w_obj, b_lean_obj_arg x) {
    if (LEAN_UNLIKELY(!lean_is_scalar(w_obj))) {
        lean_internal_panic_out_of_memory();
    }
    size_t w = lean_unbox(w_obj);

    lean_obj_res e_obj = lean_alloc_sarray1(1, w);
    nat_export_to_bytes_lsb(w, lean_sarray_cptr(e_obj), x);
    return e_obj;
}