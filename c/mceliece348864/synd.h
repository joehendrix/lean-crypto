/*
  This file is for syndrome computation
*/

#ifndef SYND_H
#define SYND_H
#define synd CRYPTO_NAMESPACE(synd)

#include "gf.h"

void synd(gf *, gf *, gf *, unsigned char *);

#endif

