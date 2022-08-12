
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