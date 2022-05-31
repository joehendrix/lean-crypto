
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
#include "pk_gen.h"
#include "util.h"

#include <openssl/conf.h>
#include <openssl/evp.h>
#include <openssl/err.h>

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

static
void handleErrors(void)
{
    ERR_print_errors_fp(stderr);
    abort();
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

extern "C" lean_obj_res lean_random_bits(b_lean_obj_arg drbg_obj, b_lean_obj_arg size) {
    if (LEAN_UNLIKELY(!lean_is_scalar(size))) {
        lean_internal_panic_out_of_memory();
    }
    size_t size_val = lean_unbox(size);
    // Currently we require bits are a multiple of 8.
    assert (size_val % 8 == 0);
    size_t xlen = size_val / 8;

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


extern "C" lean_obj_res lean_shake256(b_lean_obj_arg size_obj, b_lean_obj_arg in_obj) {
    if (LEAN_UNLIKELY(!lean_is_scalar(size_obj))) {
        lean_internal_panic_out_of_memory();
    }
    size_t size = lean_unbox(size_obj);
    lean_obj_res r_obj = lean_alloc_sarray1(1, size);

    shake(lean_sarray_cptr(r_obj), size, lean_sarray_cptr(in_obj), lean_sarray_size(in_obj));

    return r_obj;
}

extern "C" lean_obj_res lean_load_gf_array(b_lean_obj_arg r_obj) {
    lean_obj_res f_obj = lean_alloc_sarray1(2, SYS_T);
    gf* f = reinterpret_cast<gf*>(lean_sarray_cptr(f_obj));

    unsigned char* rp = lean_sarray_cptr(r_obj);
    for (size_t i = 0; i < SYS_T; i++)
        f[i] = load_gf(rp + i*2);
    return f_obj;
}

extern "C" lean_obj_res lean_genpoly_gen(b_lean_obj_arg f_obj) {
    gf* f = reinterpret_cast<gf*>(lean_sarray_cptr(f_obj));


    lean_obj_res irr_obj = lean_alloc_sarray1(2, SYS_T);
    gf* irr = reinterpret_cast<gf*>(lean_sarray_cptr(irr_obj));

    if (genpoly_gen(irr, f)) {
        return lean_mk_option_none();
    } else {
        return lean_mk_option_some(irr_obj);
    }
}

extern "C" lean_obj_res lean_load4_array(b_lean_obj_arg r_obj) {
    lean_obj_res perm_obj = lean_alloc_sarray1(4, 1 << GFBITS);
    uint32_t* perm = reinterpret_cast<uint32_t*>(lean_sarray_cptr(perm_obj));

    unsigned char* rp = lean_sarray_cptr(r_obj);
    for (size_t i = 0; i < (1 << GFBITS); i++)
        perm[i] = load4(rp + i*4);
    return perm_obj;
}

extern "C" lean_obj_res lean_store_gf(b_lean_obj_arg irr_obj) {
    gf* irr = reinterpret_cast<gf*>(lean_sarray_cptr(irr_obj));

    lean_obj_res sk_obj = lean_alloc_sarray1(1, 2 * SYS_T);
    uint8_t* sk = lean_sarray_cptr(sk_obj);

    // generating irreducible polynomial
    for (size_t i = 0; i < SYS_T; i++)
        store_gf(sk + i*2, irr[i]);

    return sk_obj;
}

extern "C" lean_obj_res lean_pk_gen(b_lean_obj_arg sk_obj, b_lean_obj_arg perm_obj) {
    uint8_t* sk = lean_sarray_cptr(sk_obj);
    assert(lean_sarray_size(sk_obj) == 2 * SYS_T);

    uint32_t* perm = reinterpret_cast<uint32_t*>(lean_sarray_cptr(perm_obj));

    lean_obj_res pk_obj = lean_alloc_sarray1(1, crypto_kem_PUBLICKEYBYTES);
    uint8_t* pk = lean_sarray_cptr(pk_obj);

    lean_obj_res pi_obj = lean_alloc_sarray1(1, 2 * (1 << GFBITS));
    int16_t* pi = reinterpret_cast<int16_t*>(lean_sarray_cptr(pi_obj));

    if (pk_gen(pk, sk, perm, pi)) {
        return lean_mk_option_none();
    }

    return lean_mk_option_some(lean_mk_pair(pk_obj, pi_obj));
}

extern "C" lean_obj_res lean_controlbitsfrompermutation(b_lean_obj_arg pi_obj) {
    lean_obj_res sk_obj = lean_alloc_sarray1(1, COND_BYTES);
    uint8_t* sk = lean_sarray_cptr(sk_obj);

    const int16_t* pi = reinterpret_cast<int16_t*>(lean_sarray_cptr(pi_obj));

    controlbitsfrompermutation(sk, pi, GFBITS, 1 << GFBITS);

    return sk_obj;
}

static inline unsigned char same_mask(uint16_t x, uint16_t y)
{
	uint32_t mask;

	mask = x ^ y;
	mask -= 1;
	mask >>= 31;
	mask = -mask;

	return mask & 0xFF;
}

static
uint16_t my_load_gf(const unsigned char *src)
{
	return ((((uint16_t) src[1]) << 8) | ((uint16_t) src[0])) & GFMASK;
}

static bool gen_e_step1(uint16_t* ind, const uint8_t* bytes) {

    uint16_t nums[ SYS_T*2 ];
    for (int i = 0; i < SYS_T*2; i++) {
        nums[i] = my_load_gf(bytes + 2*i);
    }

    // moving and counting indices in the correct range

    int count = 0;
    for (int i = 0; i < SYS_T*2 && count < SYS_T; i++)
        if (nums[i] < SYS_N)
            ind[ count++ ] = nums[i];

    if (count < SYS_T) {
        return false;
    } else {
        // check for repetition
        int eq = 0;
        for (int i = 1; i < SYS_T; i++)
            for (int j = 0; j < i; j++)
                if (ind[i] == ind[j])
                    eq = 1;

        return (eq == 0);
    }
}

extern "C" lean_obj_res lean_crypto_gen_e_step1(b_lean_obj_arg bytes_array) {
    lean_obj_res ind_array = lean_alloc_sarray1(2, SYS_T);
    uint16_t* ind = reinterpret_cast<uint16_t*>(lean_sarray_cptr(ind_array));
    uint8_t* bytes = lean_sarray_cptr(bytes_array);
	if (gen_e_step1(ind, bytes)) {
        return lean_mk_option_some(ind_array);
    } else {
        lean_free_object(ind_array);
        return lean_mk_option_none();
    }
}

static void gen_e_step2(unsigned char* val, const uint16_t* ind) {
	for (int j = 0; j < SYS_T; j++)
		val[j] = 1 << (ind[j] & 7);
}

extern "C" lean_obj_res lean_crypto_gen_e_step2(b_lean_obj_arg ind_array) {
    lean_obj_res val_array = lean_alloc_sarray1(1, SYS_T);
    uint8_t* val = lean_sarray_cptr(val_array);
    const uint16_t* ind = reinterpret_cast<uint16_t*>(lean_sarray_cptr(ind_array));
	gen_e_step2(val, ind);
    return val_array;
}

// e has length SYS_N/8
// ind has length SYS_T
// val has length SYS_T
static void gen_e_step3(unsigned char* e, const uint16_t* ind, const unsigned char* val) {
	for (int i = 0; i < SYS_N/8; i++) {
		e[i] = 0;

		for (int j = 0; j < SYS_T; j++) {
            unsigned char mask = same_mask(i, (ind[j] >> 3));
			e[i] |= val[j] & mask;
		}
	}
}

extern "C" lean_obj_res lean_crypto_gen_e_step3(b_lean_obj_arg ind_array, b_lean_obj_arg val_array) {
    lean_obj_res e_array = lean_alloc_sarray1(1, SYS_N/8);
    uint8_t* e = lean_sarray_cptr(e_array);

    const uint16_t* ind = reinterpret_cast<uint16_t*>(lean_sarray_cptr(ind_array));
    const uint8_t* val = lean_sarray_cptr(val_array);

	gen_e_step3(e, ind, val);

    return e_array;
}

/* input: public key pk, error vector e */
/* output: syndrome s */
static void syndrome(unsigned char *s, const unsigned char *pk, unsigned char *e)
{
	unsigned char b, row[SYS_N/8];
	const unsigned char *pk_ptr = pk;

	int i, j;

	for (i = 0; i < SYND_BYTES; i++)
		s[i] = 0;

	for (i = 0; i < PK_NROWS; i++)
	{
		for (j = 0; j < SYS_N/8; j++)
			row[j] = 0;

		for (j = 0; j < PK_ROW_BYTES; j++)
			row[ SYS_N/8 - PK_ROW_BYTES + j ] = pk_ptr[j];

		row[i/8] |= 1 << (i%8);

		b = 0;
		for (j = 0; j < SYS_N/8; j++)
			b ^= row[j] & e[j];

		b ^= b >> 4;
		b ^= b >> 2;
		b ^= b >> 1;
		b &= 1;

		s[ i/8 ] |= (b << (i%8));

		pk_ptr += PK_ROW_BYTES;
	}
}

extern "C" lean_obj_res lean_crypto_syndrome(b_lean_obj_arg pk_array, b_lean_obj_arg e_array) {
    uint8_t* pk = lean_sarray_cptr(pk_array);
    uint8_t* e = lean_sarray_cptr(e_array);

    lean_obj_res s_array = lean_alloc_sarray1(1, SYND_BYTES);
    uint8_t* s = lean_sarray_cptr(s_array);

	syndrome(s, pk, e);

    return s_array;
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