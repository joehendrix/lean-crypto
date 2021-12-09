/*
  This file is for functions for field arithmetic
*/

#ifndef GF_H
#define GF_H
#define gf_add CRYPTO_NAMESPACE(gf_add)
#define gf_frac CRYPTO_NAMESPACE(gf_frac)
#define gf_inv CRYPTO_NAMESPACE(gf_inv)
#define gf_iszero CRYPTO_NAMESPACE(gf_iszero)
#define gf_mul CRYPTO_NAMESPACE(gf_mul)
#define GF_mul CRYPTO_NAMESPACE(GF_mul)

#include <stdint.h>

typedef uint16_t gf;

gf gf_iszero(gf);
gf gf_add(gf, gf);
gf gf_mul(gf, gf);
gf gf_frac(gf, gf);
gf gf_inv(gf);

void GF_mul(gf *, gf *, gf *);

#endif

