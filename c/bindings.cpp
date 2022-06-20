
#define CRYPTO_NAMESPACE(x) x
#include <lean/lean.h>
#include <stdlib.h>
#include <string.h>
extern "C" {
#include "crypto_hash.h"
#include "gf.h"
#include "int32_sort.h"
#include "params.h"
#include "util.h"

#include <openssl/conf.h>
#include <openssl/evp.h>
#include <openssl/err.h>
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

static
void handleErrors(void)
{
    ERR_print_errors_fp(stderr);
    abort();
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

/*
   Use whatever AES implementation you have. This uses AES from openSSL library
      key - 256-bit AES key
      ctr - a 128-bit plaintext value
      buffer - a 128-bit ciphertext value
*/
static void
AES256_ECB(const unsigned char *key, const unsigned char *ctr, unsigned char *buffer) {
    EVP_CIPHER_CTX *ctx;

    int len;

    /* Create and initialise the context */
    if(!(ctx = EVP_CIPHER_CTX_new())) handleErrors();

    if(1 != EVP_EncryptInit_ex(ctx, EVP_aes_256_ecb(), NULL, key, NULL))
        handleErrors();

    if(1 != EVP_EncryptUpdate(ctx, buffer, &len, ctr, 16))
        handleErrors();

    /* Clean up */
    EVP_CIPHER_CTX_free(ctx);
}

extern "C" lean_obj_res lean_AES256_ECB(b_lean_obj_arg key_obj, b_lean_obj_arg v_obj) {
    assert(lean_sarray_size(key_obj) == 32);
    const uint8_t* key = lean_sarray_cptr(key_obj);

    assert(lean_sarray_size(v_obj) == 16);
    const uint8_t* v = lean_sarray_cptr(v_obj);

    lean_obj_res r_obj = lean_alloc_sarray1(1, 16);
    uint8_t* r = lean_sarray_cptr(r_obj);

    AES256_ECB(key, v, r);
    return r_obj;
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

extern "C" uint16_t lean_gf_mul(uint16_t x, uint16_t y) {
    return gf_mul(x, y);
}

extern "C" uint16_t lean_gf_frac(uint16_t x, uint16_t y) {
    return gf_frac(x, y);
}

extern "C"
uint16_t lean_gf_inv(uint16_t x) {
    gf inv = gf_inv(x);
    return inv;
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
static void cbrecursion(unsigned char *out,long long pos,long long step,const int16_t *pi,long long w,long long n,int32_t *temp) {
    // A refers to the first n elements in temp.
    int32_t* A = temp;
    // B refers tot he second n elemnts in temp.
    int32_t* B = temp+n;


    if (w == 1) {
        out[pos>>3] ^= pi[0]<<(pos&7);
        return;
    }

    for (long long x = 0;x < n;++x)
        A[x] = ((pi[x]^1)<<16)|pi[x^1];


    int32_sort(A,n); /* A = (id<<16)+pibar */

    for (long long x = 0; x < n; ++x) {
        int32_t Ax = A[x];
        int32_t px = Ax&0xffff;
        int32_t cx = px;
        if (x < cx) cx = x;
        B[x] = (px<<16)|cx;
    }
    /* B = (p<<16)+c */

    for (long long x = 0; x < n; ++x)
        A[x] = (A[x]<<16)|x; /* A = (pibar<<16)+id */
    int32_sort(A,n); /* A = (id<<16)+pibar^-1 */

    for (long long x = 0; x < n; ++x)
        A[x] = (A[x]<<16)+(B[x]>>16); /* A = (pibar^(-1)<<16)+pibar */
    int32_sort(A,n); /* A = (id<<16)+pibar^2 */

    if (w <= 10) {
        for (long long x = 0;x < n;++x)
            B[x] = ((A[x]&0xffff)<<10)|(B[x]&0x3ff);

        for (long long i = 1;i < w-1;++i) {
            /* B = (p<<10)+c */

            for (long long x = 0; x < n; ++x)
                A[x] = ((B[x]&~0x3ff)<<6)|x; /* A = (p<<16)+id */
            int32_sort(A,n); /* A = (id<<16)+p^{-1} */

            for (long long x = 0;x < n;++x)
                A[x] = (A[x]<<20)|B[x]; /* A = (p^{-1}<<20)+(p<<10)+c */
            int32_sort(A,n); /* A = (id<<20)+(pp<<10)+cp */

            for (long long x = 0; x < n; ++x) {
                int32_t ppcpx = A[x]&0xfffff;
                int32_t ppcx = (A[x]&0xffc00)|(B[x]&0x3ff);
                if (ppcpx < ppcx) ppcx = ppcpx;
                B[x] = ppcx;
            }
        }
        for (long long x = 0;x < n;++x)
            B[x] &= 0x3ff;
    } else {
        for (long long x = 0;x < n;++x)
            B[x] = (A[x]<<16)|(B[x]&0xffff);

        for (long long i = 1;i < w-1;++i) {
            /* B = (p<<16)+c */

            for (long long x = 0;x < n;++x)
                A[x] = (B[x]&~0xffff)|x;
            int32_sort(A,n); /* A = (id<<16)+p^(-1) */

            for (long long x = 0;x < n;++x)
                A[x] = (A[x]<<16)|(B[x]&0xffff);
            /* A = p^(-1)<<16+c */

            if (i < w-2) {
                for (long long x = 0;x < n;++x)
                    B[x] = (A[x]&~0xffff)|(B[x]>>16);
                /* B = (p^(-1)<<16)+p */
                int32_sort(B,n); /* B = (id<<16)+p^(-2) */
                for (long long x = 0; x < n; ++x)
                    B[x] = (B[x]<<16)|(A[x]&0xffff);
                /* B = (p^(-2)<<16)+c */
            }

            int32_sort(A,n);
            /* A = id<<16+cp */
            for (long long x = 0;x < n;++x) {
                int32_t cpx = (B[x]&~0xffff)|(A[x]&0xffff);
                if (cpx < B[x]) B[x] = cpx;
            }
        }
        for (long long x = 0;x < n;++x) B[x] &= 0xffff;
    }

    for (long long x = 0;x < n;++x) A[x] = (((int32_t)pi[x])<<16)+x;
    int32_sort(A,n); /* A = (id<<16)+pi^(-1) */

    for (long long j = 0;j < n/2;++j) {
        long long x = 2*j;
        int32_t fj = B[x]&1; /* f[j] */
        int32_t Fx = x+fj; /* F[x] */
        int32_t Fx1 = Fx^1; /* F[x+1] */

        out[pos>>3] ^= fj<<(pos&7);
        pos += step;

        B[x] = (A[x]<<16)|Fx;
        B[x+1] = (A[x+1]<<16)|Fx1;
    }
    /* B = (pi^(-1)<<16)+F */
    int32_sort(B,n); /* B = (id<<16)+F(pi) */

    pos += (2*w-3)*step*(n/2);

    for (long long k = 0;k < n/2;++k) {
        long long y = 2*k;
        int32_t lk = B[y]&1; /* l[k] */
        int32_t Ly = y+lk; /* L[y] */
        int32_t Ly1 = Ly^1; /* L[y+1] */

        out[pos>>3] ^= lk<<(pos&7);
        pos += step;

        A[y] = (Ly<<16)|(B[y]&0xffff);
        A[y+1] = (Ly1<<16)|(B[y+1]&0xffff);
    }
    /* A = (L<<16)+F(pi) */

    int32_sort(A,n); /* A = (id<<16)+F(pi(L)) = (id<<16)+M */

    // We will only need n elements in temp in recursive calls (instead of 2*n)
    // and we no longer need B, so we use it for storing new pi value.
    // q has n int16_t elements, so it only need n/2 int32_t elements from B.
    /* q can start anywhere between temp+n and temp+n+n/2 */
    int16_t* q = (int16_t *) (B);

    pos -= (2*w-2)*step*(n/2);
    for (long long j = 0;j < n/2;++j) {
        q[j] = (A[2*j]&0xffff)>>1;
        q[j+n/2] = (A[2*j+1]&0xffff)>>1;
    }

    cbrecursion(out,pos,step*2,q,w-1,n/2,temp);
    cbrecursion(out,pos+step,step*2,q+n/2,w-1,n/2,temp);
}

extern "C" lean_obj_res lean_controlbitsfrompermutation2(b_lean_obj_arg pi_obj) {
    const size_t perm_count = 1 << GFBITS;
    assert(lean_array_size(pi_obj) == perm_count);
    gf pi[perm_count];
    init_gf_array(pi, pi_obj);

    lean_obj_res out_obj = lean_alloc_sarray1(1, COND_BYTES);
    uint8_t* out = lean_sarray_cptr(out_obj);

    long long w = GFBITS;
    long long n = 1 << GFBITS;

    int32_t temp[2*n];
    memset(out,0, COND_BYTES);
    cbrecursion(out,0,1,(int16_t*)pi,w,n,temp);

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