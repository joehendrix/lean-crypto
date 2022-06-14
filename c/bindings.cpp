
#define CRYPTO_NAMESPACE(x) x
#include <lean/lean.h>
#include <stdlib.h>
#include <string.h>
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
#include "uint64_sort.h"
#include "util.h"
#include "transpose.h"

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
AES256_ECB(unsigned char *key, unsigned char *ctr, unsigned char *buffer)
{
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

inline static lean_obj_res lean_mk_pair(lean_obj_arg x, lean_obj_arg y) {
    lean_object * r = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(r, 0, x);
    lean_ctor_set(r, 1, y);
    return r;
}

static void
my_AES256_CTR_DRBG_Update(unsigned char *provided_data,
                       unsigned char *Key,
                       unsigned char *V)
{
    unsigned char   temp[48];
    int i;
    int j;

    for (i=0; i<3; i++) {
        /* increment V */
        for (j=15; j>=0; j--) {
            if ( V[j] == 0xff )
                V[j] = 0x00;
            else {
                V[j]++;
                break;
            }
        }

        AES256_ECB(Key, V, temp+16*i);
    }
    if ( provided_data != NULL )
        for (i=0; i<48; i++)
            temp[i] ^= provided_data[i];
    memcpy(Key, temp, 32);
    memcpy(V, temp+32, 16);
}

extern "C" lean_obj_res lean_random_init(b_lean_obj_arg entropy_input_array) {
    assert(lean_sarray_size(entropy_input_array) == 48);
    unsigned char* entropy_input = lean_sarray_cptr(entropy_input_array);

    lean_obj_res key_array = lean_alloc_sarray1(1, 32);
    uint8_t* key = lean_sarray_cptr(key_array);

    lean_obj_res v_array = lean_alloc_sarray1(1, 16);
    uint8_t* v = lean_sarray_cptr(v_array);

    unsigned char   seed_material[48];
    memcpy(seed_material, entropy_input, 48);
    memset(key, 0x00, 32);
    memset(v, 0x00, 16);
    my_AES256_CTR_DRBG_Update(seed_material, key, v);
    return lean_mk_pair(key_array, v_array);
}

extern "C" lean_obj_res lean_random_bytes(b_lean_obj_arg drbg_obj, b_lean_obj_arg size) {
    if (LEAN_UNLIKELY(!lean_is_scalar(size))) {
        lean_internal_panic_out_of_memory();
    }
    size_t xlen = lean_unbox(size);

    uint8_t* key_input = lean_sarray_cptr(lean_ctor_get(drbg_obj, 0));
    lean_obj_res key_array = lean_alloc_sarray1(1, 32);
    uint8_t* key = lean_sarray_cptr(key_array);
    memcpy(key, key_input, 32);

    uint8_t* v_input   = lean_sarray_cptr(lean_ctor_get(drbg_obj, 1));
    lean_obj_res v_array = lean_alloc_sarray1(1, 16);
    uint8_t* v = lean_sarray_cptr(v_array);
    memcpy(v, v_input, 16);

    lean_obj_res r = lean_alloc_sarray1(1, xlen);
    uint8_t* x = lean_sarray_cptr(r);

    unsigned char   block[16];
    int             i = 0;
    int j;

    while ( xlen > 0 ) {
        /* increment V */
        for (j=15; j>=0; j--) {
            if ( v[j] == 0xff )
                v[j] = 0x00;
            else {
                v[j]++;
                break;
            }
        }
        AES256_ECB(key, v, block);
        if ( xlen > 15 ) {
            memcpy(x+i, block, 16);
            i += 16;
            xlen -= 16;
        }
        else {
            memcpy(x+i, block, xlen);
            xlen = 0;
        }
    }
    my_AES256_CTR_DRBG_Update(NULL, key, v);

    return lean_mk_pair(r, lean_mk_pair(key_array, v_array));
}

inline static lean_obj_res lean_mk_option_none(void) {
    return lean_alloc_ctor(0, 0, 0);
}

inline static lean_obj_res lean_mk_option_some(lean_obj_arg v) {
    lean_object * r = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(r, 0, v);
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

extern "C" lean_obj_res lean_controlbitsfrompermutation(b_lean_obj_arg pi_obj) {

    const size_t perm_count = 1 << GFBITS;
    assert(lean_array_size(pi_obj) == perm_count);
    int16_t pi[perm_count];
    for (size_t i = 0; i != perm_count; ++i) {
        pi[i] = lean_unbox_uint32(lean_array_get_core(pi_obj, i));
    }

    lean_obj_res sk_obj = lean_alloc_sarray1(1, COND_BYTES);
    uint8_t* sk = lean_sarray_cptr(sk_obj);

    controlbitsfrompermutation(sk, pi, GFBITS, 1 << GFBITS);

    return sk_obj;
}

extern "C" gf bitrev(gf a);

#define min(a, b) ((a < b) ? a : b)

/* one layer of the benes network */
static void layer(uint64_t * data, uint64_t * bits, int lgs) {
	int i, j, s;

	uint64_t d;

	s = 1 << lgs;

	for (i = 0; i < 64; i += s*2)
	for (j = i; j < i+s; j++)
	{

		d = (data[j+0] ^ data[j+s]);
		d &= (*bits++);
		data[j+0] ^= d;
		data[j+s] ^= d;
	}
}

/* input: r, sequence of bits to be permuted */
/*        bits, condition bits of the Benes network */
/*        rev, 0 for normal application; !0 for inverse */
/* output: r, permuted bits */
void my_apply_benes0(unsigned char * r2, const unsigned char * bits) {


	uint64_t bs[64];
	for (int i = 0; i < 64; i++) {
		bs[i] = load8(r2 + i*8);
	}


    int inc = 256;
	const unsigned char *cond_ptr = bits;

	transpose_64x64(bs, bs);

	uint64_t cond[64];
	for (int low = 0; low <= 5; low++) {
		for (int i = 0; i < 64; i++)
            cond[i] = load4(cond_ptr + i*4);
		transpose_64x64(cond, cond);
		layer(bs, cond, low);
		cond_ptr += inc;
	}

	transpose_64x64(bs, bs);

	for (int low = 0; low <= 5; low++) {
		for (int i = 0; i < 32; i++)
            cond[i] = load8(cond_ptr + i*8);
		layer(bs, cond, low);
		cond_ptr += inc;
	}
	for (int low = 4; low >= 0; low--) {
		for (int i = 0; i < 32; i++)
            cond[i] = load8(cond_ptr + i*8);
		layer(bs, cond, low);
		cond_ptr += inc;
	}

	transpose_64x64(bs, bs);

	for (int low = 5; low >= 0; low--) {
		for (int i = 0; i < 64; i++)
            cond[i] = load4(cond_ptr + i*4);
		transpose_64x64(cond, cond);
		layer(bs, cond, low);
		cond_ptr += inc;
	}

	transpose_64x64(bs, bs);

	for (int i = 0; i < 64; i++) {
		store8(r2 + i*8, bs[i]);
	}
}

extern "C" lean_obj_res lean_apply_benes0(b_lean_obj_arg r_obj, b_lean_obj_arg c_obj) {
    assert(lean_sarray_size(c_obj) == COND_BYTES);
    const uint8_t* c = lean_sarray_cptr(c_obj);

    unsigned char r[(1 << GFBITS)/8];
    nat_export_to_bytes((1 << GFBITS)/8, r, r_obj);

	my_apply_benes0(r, c);

    return nat_import_from_bytes((1 << GFBITS)/8, r);
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