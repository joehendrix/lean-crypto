
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
        printf("UNEXPECTED %d\n", n);
        assert(0);
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

extern "C" uint16_t lean_gf_add(uint16_t x, uint16_t y) {
    return gf_add(x, y);
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
    for (size_t i = 0; i != SYS_T+1; ++i) {
        g[i] = lean_unbox_uint32(lean_array_get_core(g_obj, i));
    }
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

/* input: public key pk, error vector e */
/* output: syndrome s */
static void syndrome(unsigned char *s, const unsigned char *pk, unsigned char *e)
{

	for (int i = 0; i < SYND_BYTES; i++)
		s[i] = 0;

	for (int i = 0; i < PK_NROWS; i++) {
    	const unsigned char *pk_ptr = pk + PK_ROW_BYTES * i;

        unsigned char row[SYS_N/8];
		for (int j = 0; j < SYS_N/8; j++)
			row[j] = 0;

		for (int j = 0; j < PK_ROW_BYTES; j++)
			row[ SYS_N/8 - PK_ROW_BYTES + j ] = pk_ptr[j];

		row[i/8] |= 1 << (i%8);

    	unsigned char b = 0;
		for (int j = 0; j < SYS_N/8; j++)
			b ^= row[j] & e[j];

		b ^= b >> 4;
		b ^= b >> 2;
		b ^= b >> 1;
		b &= 1;

        s[ i/8 ] |= (b << (i%8));
	}
}

extern "C" lean_obj_res lean_crypto_syndrome(b_lean_obj_arg pk_array, b_lean_obj_arg e_obj) {
    uint8_t* pk = lean_sarray_cptr(pk_array);

	unsigned char e[SYS_N/8];
    nat_export_to_bytes(SYS_N/8, e, e_obj);

    unsigned char s[SYND_BYTES];
	syndrome(s, pk, e);
    return nat_import_from_bytes(SYND_BYTES, s);
}

extern "C" void bm(gf *, gf *);
extern "C" void support_gen(gf *, const unsigned char *);

extern "C" gf bitrev(gf a);
extern "C" void apply_benes(unsigned char * r, const unsigned char * bits, int rev);


/* input: condition bits c */
/* output: support s */
void my_support_gen(gf * s, const unsigned char *c) {
	unsigned char L[ GFBITS ][ (1 << GFBITS)/8 ];
	for (int i = 0; i < GFBITS; i++)
		for (int j = 0; j < (1 << GFBITS)/8; j++)
			L[i][j] = 0;

	for (int i = 0; i < (1 << GFBITS); i++)
	{
		gf a = bitrev((gf) i);

		for (int j = 0; j < GFBITS; j++)
			L[j][ i/8 ] |= ((a >> j) & 1) << (i%8);
	}

	for (int j = 0; j < GFBITS; j++)
		apply_benes(L[j], c, 0);

	for (int i = 0; i < SYS_N; i++) {
		s[i] = 0;
		for (int j = GFBITS-1; j >= 0; j--)
		{
			s[i] <<= 1;
			s[i] |= (L[j][i/8] >> (i%8)) & 1;
		}
	}
}

#define min(a, b) ((a < b) ? a : b)

/* the Berlekamp-Massey algorithm */
/* input: s, sequence of field elements */
/* output: out, minimal polynomial of s */
static
void my_bm(gf *out, const gf *s)
{
	//

	gf B[SYS_T+1];
	for (int i = 0; i < SYS_T+1; i++)
		B[i] = 0;
	B[1] = 1;

	gf C[SYS_T+1];
	for (int i = 0; i < SYS_T+1; i++)
		C[i] = 0;
	C[0] = 1;


	uint16_t L = 0;
	gf b = 1;

	//
	for (uint16_t N = 0; N < 2 * SYS_T; N++) {
		gf d = 0;
		for (int i = 0; i <= min(N, SYS_T); i++)
			d ^= gf_mul(C[i], s[ N-i]);

		gf mne = ((d-1)>>15)-1;
        gf mle = N; mle -= 2*L; mle >>= 15; mle -= 1;
		mle &= mne;

    	gf T[ SYS_T+1  ];
		for (int i = 0; i <= SYS_T; i++)
			T[i] = C[i];

        gf f = gf_frac(b, d);

		for (int i = 0; i <= SYS_T; i++)
			C[i] ^= gf_mul(f, B[i]) & mne;

		L = (L & ~mle) | ((N+1-L) & mle);

		for (int i = 0; i <= SYS_T; i++)
			B[i] = (B[i] & ~mle) | (T[i] & mle);

		b = (b & ~mle) | (d & mle);

		for (int i = SYS_T; i >= 1; i--)
            B[i] = B[i-1];
		B[0] = 0;
	}

	for (int i = 0; i <= SYS_T; i++)
		out[i] = C[ SYS_T-i ];
}

/* Niederreiter decryption with the Berlekamp decoder */
// intput: g, goppy poly
//         sk, secret key
//         c, ciphertext
// output: e, error vector
// return: 0 for success; 1 for failure
static int my_decrypt(unsigned char *e,
                      gf* images,
                      const gf* s)
{
	//

	for (int i = 0; i < SYS_N/8; i++)
		e[i] = 0;

	int w = 0;
	for (int i = 0; i < SYS_N; i++) {
	    gf t = gf_iszero(images[i]) & 1;

		e[ i/8 ] |= t << (i%8);
		w += t;
	}

    return w;
}

extern "C" lean_obj_res lean_support_gen(b_lean_obj_arg sk_obj) {
    assert(lean_sarray_size(sk_obj) == COND_BYTES);
    const uint8_t* sk = lean_sarray_cptr(sk_obj);

	gf L[ SYS_N ];
	support_gen(L, sk);

    lean_obj_res L_obj = lean_alloc_array(SYS_N, SYS_N);
    for (size_t i = 0; i != SYS_N; ++i) {
        lean_array_set_core(L_obj, i, lean_box_uint32(L[i]));
    }
    return L_obj;
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

static void init_gf_array(gf* s, b_lean_obj_arg obj) {
    for (size_t i = 0; i != lean_array_size(obj); ++i) {
        s[i] = lean_unbox_uint32(lean_array_get_core(obj, i));
    }
}

extern "C" lean_obj_res lean_bm(b_lean_obj_arg s_obj, b_lean_obj_arg s2_obj) {
    assert(lean_array_size(s_obj) == 2*SYS_T);
	gf s[2*SYS_T];
    init_gf_array(s, s_obj);

	gf locator[ SYS_T+1 ];
	my_bm(locator, s);

    lean_obj_res locator_obj = lean_alloc_array(SYS_T+1, SYS_T+1);
    for (size_t i = 0; i != SYS_T+1; ++i) {
        lean_array_set_core(locator_obj, i, lean_box_uint32(locator[i]));
    }
    return locator_obj;
}

extern "C" lean_obj_res lean_decrypt(b_lean_obj_arg images_obj, b_lean_obj_arg s_obj) {
    assert(lean_array_size(images_obj) == SYS_N);
	gf images[SYS_N];
    for (size_t i = 0; i != SYS_N; ++i) {
        images[i] = lean_unbox_uint32(lean_array_get_core(images_obj, i));
    }

   assert(lean_array_size(s_obj) == 2*SYS_T);
	gf s[2*SYS_T];
    for (size_t i = 0; i != 2*SYS_T; ++i) {
        s[i] = lean_unbox_uint32(lean_array_get_core(s_obj, i));
    }


    uint8_t e[SYS_N/8];
    int w = my_decrypt(e, images, s);
    return lean_mk_pair(lean_box(w), nat_import_from_bytes(SYS_N/8, e));
}