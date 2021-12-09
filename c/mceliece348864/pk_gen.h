/*
  This file is for public-key generation
*/

#ifndef PK_GEN_H
#define PK_GEN_H
#define pk_gen CRYPTO_NAMESPACE(pk_gen)

#include "gf.h"

int pk_gen(unsigned char *, unsigned char *, uint32_t *, int16_t *);

#endif

