
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
#include "root.h"
#include "uint64_sort.h"
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

extern "C" lean_obj_res lean_GF_mul(b_lean_obj_arg x_obj, b_lean_obj_arg y_obj) {

    size_t x_count = lean_array_size(x_obj);
    gf x[x_count];
    for (size_t i = 0; i != x_count; ++i) {
        x[i] = (gf) lean_unbox_uint32(lean_array_get_core(x_obj, i));
    }

    size_t y_count = lean_array_size(y_obj);
    gf y[y_count];
    for (size_t i = 0; i != y_count; ++i) {
        y[i] = (gf) lean_unbox_uint32(lean_array_get_core(y_obj, i));
    }

    gf r[SYS_T];
    GF_mul(r, x, y);

    lean_obj_res r_obj = lean_alloc_array(SYS_T, SYS_T);
    for (size_t i = 0; i != SYS_T; ++i) {
        lean_array_set_core(r_obj, i, lean_box_uint32(r[i]));
    }
    return r_obj;
}


static
void gf_mul_array1(gf* out, gf s, gf* in, size_t n) {
    for (size_t c = 0; c < n; c++) {
        out[c] = gf_mul(s, in[c]);
    }
}

static
void xor_array(gf* out, gf* x, gf* y, size_t n) {
    for (size_t c = 0; c < n; c++) {
        out[c] = x[c] ^ y[c];
    }
}

extern "C" uint16_t lean_gf_iszero(uint16_t x) {
    return gf_iszero(x);
}

extern "C"
uint16_t lean_gf_inv(uint16_t x) {
    gf inv = gf_inv(x);
    return inv;
}

extern "C" lean_obj_res lean_store_gf(b_lean_obj_arg irr_obj) {

    size_t irr_count = lean_array_size(irr_obj);
    assert(irr_count == SYS_T);
    gf irr[irr_count];
    for (size_t i = 0; i != irr_count; ++i) {
        irr[i] = (gf) lean_unbox_uint32(lean_array_get_core(irr_obj, i));
    }

    lean_obj_res sk_obj = lean_alloc_sarray1(1, 2 * SYS_T);
    uint8_t* sk = lean_sarray_cptr(sk_obj);

    // generating irreducible polynomial
    for (size_t i = 0; i < SYS_T; i++)
        store_gf(sk + i*2, irr[i]);

    return sk_obj;
}

/* input: polynomial f and field element a */
/* return f(a) */
static
gf my_eval(const gf *f, gf a) {
	gf r = f[ SYS_T ];

	for (int i = SYS_T-1; i >= 0; i--) {
		r = gf_mul(r, a);
		r = gf_add(r, f[i]);
	}

	return r;
}

static
int gaussian_elim_row(unsigned char** out, const unsigned char** mat, int row) {
    int i = row / 8;
    int j = row % 8;

    unsigned char mat_row[ SYS_N/8 ];
    for (size_t c = 0; c < SYS_N/8; c++)
        mat_row[c] = mat[row][c];

    for (size_t k = row + 1; k < PK_NROWS; k++) {
        unsigned char mask = mat_row[i] ^ mat[k][i];
        mask >>= j;
        mask &= 1;
        mask = -mask;

        for (size_t c = 0; c < SYS_N/8; c++)
            mat_row[c] ^= mat[k][c] & mask;
    }

    if ( ((mat_row[ i ] >> j) & 1) == 0 ) // return if not systematic
    {
        return -1;
    }


    for (size_t k = 0; k < PK_NROWS; k++) {
        if (k == row) {
            for (size_t c = 0; c < SYS_N/8; c++)
                out[k][c] = mat_row[c];
        } else {
            unsigned char mask;
            mask = mat[ k ][ i ] >> j;
            mask &= 1;
            mask = -mask;

            for (size_t c = 0; c < SYS_N/8; c++)
                out[k][c] = mat[k][c] ^ mat_row[c] & mask;
        }
    }
    return 0;
}

extern "C" lean_obj_res lean_gaussian_elim_row(b_lean_obj_arg mat_obj, b_lean_obj_arg r_obj) {
    const size_t n = PK_NROWS * SYS_N/8;
    assert(lean_array_size(mat_obj) == n);

	unsigned char mats[ PK_NROWS ][ SYS_N/8 ];
    for (size_t i = 0; i != PK_NROWS; ++i) {
        for (size_t j = 0; j != SYS_N/8; ++j) {
            mats[i][j] = lean_unbox_uint32(lean_array_get_core(mat_obj, i * (SYS_N/8) + j));
        }
    }

	const unsigned char* mat[PK_NROWS];
    for (size_t i = 0; i < PK_NROWS; ++i) {
        mat[i] = mats[i];
    }

	unsigned char outs[PK_NROWS][SYS_N/8];
	unsigned char* out[PK_NROWS];
    for (size_t i = 0; i < PK_NROWS; ++i)
        out[i] = outs[i];

    size_t r = lean_unbox(r_obj);

	// gaussian elimination
    if (gaussian_elim_row(out, mat, r))
        return lean_mk_option_none();

    lean_obj_res out_obj = lean_alloc_array(n, n);
    int out_idx = 0;
    for (int i = 0; i != PK_NROWS; ++i) {
        for (int j = 0; j != SYS_N/8; ++j) {
            lean_array_set_core(out_obj, out_idx++, lean_box_uint32(outs[i][j]));
        }
    }
    return lean_mk_option_some(out_obj);
}

static
int gaussian_elim(unsigned char** mat) {
	unsigned char outs[PK_NROWS][SYS_N/8];
	unsigned char* out[PK_NROWS];
    for (size_t i = 0; i < PK_NROWS; ++i)
        out[i] = outs[i];

	const unsigned char** matr = const_cast<const unsigned char**>(mat);

	for (size_t r = 0; r < PK_NROWS; ++r) {
        if (gaussian_elim_row(out, matr, r))
            return -1;
    	for (size_t i = 0; i < PK_NROWS; ++i)
            memcpy(mat[i], out[i], SYS_N/8);
    }
    return 0;
}


static
void init_mat_row(unsigned char* matj, const gf* Lj, gf* invj) {
    for (size_t i = 0; i < SYS_T; i++) {
        for (size_t k = 0; k < GFBITS;  k++) {
            unsigned char b;
            b  = (invj[7] >> k) & 1; b <<= 1;
            b |= (invj[6] >> k) & 1; b <<= 1;
            b |= (invj[5] >> k) & 1; b <<= 1;
            b |= (invj[4] >> k) & 1; b <<= 1;
            b |= (invj[3] >> k) & 1; b <<= 1;
            b |= (invj[2] >> k) & 1; b <<= 1;
            b |= (invj[1] >> k) & 1; b <<= 1;
            b |= (invj[0] >> k) & 1;
            matj[i*GFBITS + k] = b;
        }

        for (size_t c = 0; c != 8; ++c) {
            invj[c] = gf_mul(invj[c], Lj[c]);
        }
    }
}

static
void init_mat(unsigned char** mat, const gf* L, const gf* inv) {
    for (size_t j = 0; j < SYS_N/8; ++j) {

    	unsigned char matj[PK_NROWS];

        gf invj[8];
        memcpy(invj, inv + 8*j, 8*sizeof(gf));

        init_mat_row(matj, L+8*j, invj);

        for (int i = 0; i != PK_NROWS; ++i) {
            mat[i][j] = matj[i];
        }
	}
}

extern "C" lean_obj_res lean_init_mat(b_lean_obj_arg inv_obj, b_lean_obj_arg l_obj) {
    assert(lean_array_size(l_obj) == SYS_N);
    gf L[SYS_N];
    for (size_t i = 0; i != SYS_N; ++i) {
        L[i] = lean_unbox_uint32(lean_array_get_core(l_obj, i));
    }

	gf inv[ SYS_N ];
    for (size_t i = 0; i != SYS_N; ++i) {
        inv[i] = lean_unbox_uint32(lean_array_get_core(inv_obj, i));
    }

	unsigned char mats[ PK_NROWS ][ SYS_N/8 ];
	unsigned char* mat[PK_NROWS];
    for (size_t i = 0; i < PK_NROWS; ++i) {
        mat[i] = mats[i];
    }
    init_mat(mat, L, inv);

    lean_obj_res mat_obj = lean_alloc_array(PK_NROWS * SYS_N/8, PK_NROWS * SYS_N/8);
    int r = 0;
    for (int i = 0; i != PK_NROWS; ++i) {
        for (int j = 0; j != SYS_N/8; ++j) {
            lean_array_set_core(mat_obj, r++, lean_box_uint32(mats[i][j]));
        }
    }
    return mat_obj;
}

extern "C" uint16_t lean_bitrev(uint16_t x) {
    return bitrev(x);
}

extern "C"  uint16_t lean_eval(b_lean_obj_arg g_obj, uint16_t x) {
	gf g[ SYS_T+1 ]; // Goppa polynomial
    for (size_t i = 0; i != SYS_T; ++i) {
        g[i] = lean_unbox_uint32(lean_array_get_core(g_obj, i));
    }
	g[ SYS_T ] = 1;

    return my_eval(g, x);
}

extern "C" lean_obj_res lean_pk_gen3(b_lean_obj_arg inv_obj, b_lean_obj_arg l_obj) {
    assert(lean_array_size(l_obj) == SYS_N);
    gf L[SYS_N];
    for (size_t i = 0; i != SYS_N; ++i) {
        L[i] = lean_unbox_uint32(lean_array_get_core(l_obj, i));
    }

	gf inv[ SYS_N ];
    for (size_t i = 0; i != SYS_N; ++i) {
        inv[i] = lean_unbox_uint32(lean_array_get_core(inv_obj, i));
    }

	unsigned char mats[ PK_NROWS ][ SYS_N/8 ];

	unsigned char* mat[PK_NROWS];
    for (size_t i = 0; i < PK_NROWS; ++i) {
        mat[i] = mats[i];
    }

    init_mat(mat, L, inv);
	// gaussian elimination
    if (gaussian_elim(mat))
        return lean_mk_option_none();

    lean_obj_res mat_obj = lean_alloc_array(PK_NROWS * SYS_N/8, PK_NROWS * SYS_N/8);
    int r = 0;
    for (int i = 0; i != PK_NROWS; ++i) {
        for (int j = 0; j != SYS_N/8; ++j) {
            lean_array_set_core(mat_obj, r++, lean_box_uint32(mats[i][j]));
        }
    }
    return lean_mk_option_some(mat_obj);
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

static inline unsigned char same_mask_orig(uint16_t x, uint16_t y)
{
	uint32_t mask = (x ^ y) - 1;
	return (-(mask >> 31)) & 0xFF;
}


static inline unsigned char same_mask(uint16_t x, uint16_t y)
{
    if (x == y) {
    	return 0xFF;
    } else {
        return 0;
    }
}


// e has length SYS_N/8
// ind has length SYS_T
// val has length SYS_T
static void gen_e_step3(unsigned char* e, const uint16_t* ind) {
	for (int i = 0; i < SYS_N/8; i++) {
        unsigned char ei = 0;
		for (int j = 0; j < SYS_T; j++) {
            uint16_t indj = ind[j] >> 3;
			if (i == indj)
                ei = ei | (1 << (ind[j] & 7));
		}
		e[i] = ei;
	}
}


extern "C" lean_obj_res lean_crypto_gen_e_step3(b_lean_obj_arg ind_obj) {

    assert(lean_array_size(ind_obj) == SYS_T);

    uint16_t ind[SYS_T];
    for (size_t i = 0; i != SYS_T; ++i) {
        b_lean_obj_arg x = lean_array_get_core(ind_obj, i);
        if (LEAN_UNLIKELY(!lean_is_scalar(x))) {
            lean_internal_panic_out_of_memory();
        }
        size_t xlen = lean_unbox(x);
        assert(xlen <= SYS_N);
        ind[i] = xlen;
    }

    lean_obj_res e_array = lean_alloc_sarray1(1, SYS_N/8);
    uint8_t* e = lean_sarray_cptr(e_array);
	gen_e_step3(e, ind);
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

	SHAKE256(key, 32, lean_sarray_cptr(input), lean_sarray_size(input));

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