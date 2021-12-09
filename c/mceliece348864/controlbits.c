/* This file is for implementing the Nassimi-Sahni algorithm */
/* See David Nassimi, Sartaj Sahni "Parallel algorithms to set up the Benes permutationnetwork" */
/* See also https://cr.yp.to/papers/controlbits-20200923.pdf */

#include <string.h>
#include "controlbits.h"
#include "int32_sort.h"
typedef int16_t int16;
typedef int32_t int32;

/* parameters: 1 <= w <= 14; n = 2^w */
/* input: permutation pi of {0,1,...,n-1} */
/* output: (2m-1)n/2 control bits at positions pos,pos+step,... */
/* output position pos is by definition 1&(out[pos/8]>>(pos&7)) */
/* caller must 0-initialize positions first */
/* temp must have space for int32[2*n] */
static void cbrecursion(unsigned char *out,long long pos,long long step,const int16 *pi,long long w,long long n,int32 *temp)
{
#define A temp
#define B (temp+n)
#define q ((int16 *) (temp+n+n/4))
/* q can start anywhere between temp+n and temp+n/2 */

  long long x,i,j,k;

  if (w == 1) {
    out[pos>>3] ^= pi[0]<<(pos&7);
    return;
  }

  for (x = 0;x < n;++x) A[x] = ((pi[x]^1)<<16)|pi[x^1];
  int32_sort(A,n); /* A = (id<<16)+pibar */

  for (x = 0;x < n;++x) {
    int32 Ax = A[x];
    int32 px = Ax&0xffff;
    int32 cx = px;
    if (x < cx) cx = x;
    B[x] = (px<<16)|cx;
  }
  /* B = (p<<16)+c */

  for (x = 0;x < n;++x) A[x] = (A[x]<<16)|x; /* A = (pibar<<16)+id */
  int32_sort(A,n); /* A = (id<<16)+pibar^-1 */

  for (x = 0;x < n;++x) A[x] = (A[x]<<16)+(B[x]>>16); /* A = (pibar^(-1)<<16)+pibar */
  int32_sort(A,n); /* A = (id<<16)+pibar^2 */

  if (w <= 10) {
    for (x = 0;x < n;++x) B[x] = ((A[x]&0xffff)<<10)|(B[x]&0x3ff);

    for (i = 1;i < w-1;++i) {
      /* B = (p<<10)+c */

      for (x = 0;x < n;++x) A[x] = ((B[x]&~0x3ff)<<6)|x; /* A = (p<<16)+id */
      int32_sort(A,n); /* A = (id<<16)+p^{-1} */

      for (x = 0;x < n;++x) A[x] = (A[x]<<20)|B[x]; /* A = (p^{-1}<<20)+(p<<10)+c */
      int32_sort(A,n); /* A = (id<<20)+(pp<<10)+cp */

      for (x = 0;x < n;++x) {
        int32 ppcpx = A[x]&0xfffff;
        int32 ppcx = (A[x]&0xffc00)|(B[x]&0x3ff);
        if (ppcpx < ppcx) ppcx = ppcpx;
        B[x] = ppcx;
      }
    }
    for (x = 0;x < n;++x) B[x] &= 0x3ff;
  } else {
    for (x = 0;x < n;++x) B[x] = (A[x]<<16)|(B[x]&0xffff);

    for (i = 1;i < w-1;++i) {
      /* B = (p<<16)+c */

      for (x = 0;x < n;++x) A[x] = (B[x]&~0xffff)|x;
      int32_sort(A,n); /* A = (id<<16)+p^(-1) */

      for (x = 0;x < n;++x) A[x] = (A[x]<<16)|(B[x]&0xffff);
      /* A = p^(-1)<<16+c */

      if (i < w-2) {
        for (x = 0;x < n;++x) B[x] = (A[x]&~0xffff)|(B[x]>>16);
        /* B = (p^(-1)<<16)+p */
        int32_sort(B,n); /* B = (id<<16)+p^(-2) */
        for (x = 0;x < n;++x) B[x] = (B[x]<<16)|(A[x]&0xffff);
        /* B = (p^(-2)<<16)+c */
      }
  
      int32_sort(A,n);
      /* A = id<<16+cp */
      for (x = 0;x < n;++x) {
        int32 cpx = (B[x]&~0xffff)|(A[x]&0xffff);
        if (cpx < B[x]) B[x] = cpx;
      }
    }
    for (x = 0;x < n;++x) B[x] &= 0xffff;
  }

  for (x = 0;x < n;++x) A[x] = (((int32)pi[x])<<16)+x;
  int32_sort(A,n); /* A = (id<<16)+pi^(-1) */

  for (j = 0;j < n/2;++j) {
    long long x = 2*j;
    int32 fj = B[x]&1; /* f[j] */
    int32 Fx = x+fj; /* F[x] */
    int32 Fx1 = Fx^1; /* F[x+1] */

    out[pos>>3] ^= fj<<(pos&7);
    pos += step;

    B[x] = (A[x]<<16)|Fx;
    B[x+1] = (A[x+1]<<16)|Fx1;
  }
  /* B = (pi^(-1)<<16)+F */

  int32_sort(B,n); /* B = (id<<16)+F(pi) */

  pos += (2*w-3)*step*(n/2);

  for (k = 0;k < n/2;++k) {
    long long y = 2*k;
    int32 lk = B[y]&1; /* l[k] */
    int32 Ly = y+lk; /* L[y] */
    int32 Ly1 = Ly^1; /* L[y+1] */

    out[pos>>3] ^= lk<<(pos&7);
    pos += step;

    A[y] = (Ly<<16)|(B[y]&0xffff);
    A[y+1] = (Ly1<<16)|(B[y+1]&0xffff);
  }
  /* A = (L<<16)+F(pi) */

  int32_sort(A,n); /* A = (id<<16)+F(pi(L)) = (id<<16)+M */

  pos -= (2*w-2)*step*(n/2);

  for (j = 0;j < n/2;++j) {
    q[j] = (A[2*j]&0xffff)>>1;
    q[j+n/2] = (A[2*j+1]&0xffff)>>1;
  }

  cbrecursion(out,pos,step*2,q,w-1,n/2,temp);
  cbrecursion(out,pos+step,step*2,q+n/2,w-1,n/2,temp);
}

/* input: p, an array of int16 */
/* input: n, length of p */
/* input: s, meaning that stride-2^s cswaps are performed */
/* input: cb, the control bits */
/* output: the result of apply the control bits to p */
static void layer(int16_t *p, const unsigned char *cb, int s, int n)
{
  int i, j;
  int stride = 1 << s;
  int index = 0;
  int16_t d, m;

  for (i = 0; i < n; i += stride*2)
  {
    for (j = 0; j < stride; j++)
    {
      d = p[ i+j ] ^ p[ i+j+stride ];
      m = (cb[ index >> 3 ] >> (index & 7)) & 1;
      m = -m;
      d &= m;
      p[ i+j ] ^= d;
      p[ i+j+stride ] ^= d;
      index++;
    }
  }
}

/* parameters: 1 <= w <= 14; n = 2^w */
/* input: permutation pi of {0,1,...,n-1} */
/* output: (2m-1)n/2 control bits at positions 0,1,... */
/* output position pos is by definition 1&(out[pos/8]>>(pos&7)) */
void controlbitsfrompermutation(unsigned char *out,const int16 *pi,long long w,long long n)
{
  int32 temp[2*n];
  int16 pi_test[n], diff;
  int i;
  unsigned char *ptr;

  while (1)
  {
    memset(out,0,(((2*w-1)*n/2)+7)/8);
    cbrecursion(out,0,1,pi,w,n,temp);

    // check for correctness

    for (i = 0; i < n; i++)
      pi_test[i] = i;

    ptr = out;
    for (i = 0; i < w; i++)
    {
      layer(pi_test, ptr, i, n);
      ptr += n >> 4;
    }

    for (i = w-2; i >= 0; i--)
    {
      layer(pi_test, ptr, i, n);
      ptr += n >> 4;
    }

    diff = 0;
    for (i = 0; i < n; i++)
      diff |= pi[i] ^ pi_test[i];

    if (diff == 0)
      break;
  }
}

