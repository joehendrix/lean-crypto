/*
  This file is for secret-key generation
*/

#ifndef SK_GEN_H
#define SK_GEN_H
#define genpoly_gen CRYPTO_NAMESPACE(genpoly_gen)
#define perm_check CRYPTO_NAMESPACE(perm_check)

#include "gf.h"

#include <stdint.h>

int genpoly_gen(gf *, gf *);
int perm_check(uint32_t *);

#endif

