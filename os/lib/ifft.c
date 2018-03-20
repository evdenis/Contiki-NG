/*
 * Copyright (c) 2008, Swedish Institute of Computer Science
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the Institute nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE INSTITUTE AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE INSTITUTE OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 * -----------------------------------------------------------------
 * ifft - Integer FFT (fast fourier transform) library
 *
 *
 * Author  : Joakim Eriksson
 * Created : 2008-03-27
 * Updated : $Date: 2008/07/03 23:40:12 $
 *           $Revision: 1.3 $
 */

#include "contiki.h"
#include "lib/ifft.h"

/*---------------------------------------------------------------------------*/
/* constant table of sin values in 8/7 bits resolution */
/* NOTE: symmetry can be used to reduce this to 1/2 or 1/4 the size */
#define SIN_TAB_LEN 120
#define RESOLUTION 7

static const int8_t SIN_TAB[] = {
 0,6,13,20,26,33,39,45,52,58,63,69,75,80,
 85,90,95,99,103,107,110,114,116,119,121,
 123,125,126,127,127,127,127,127,126,125,
 123,121,119,116,114,110,107,103,99,95,90,
 85,80,75,69,63,58,52,45,39,33,26,20,13,6,
 0,-6,-13,-20,-26,-33,-39,-45,-52,-58,-63,
 -69,-75,-80,-85,-90,-95,-99,-103,-107,-110,
 -114,-116,-119,-121,-123,-125,-126,-127,-127,
 -127,-127,-127,-126,-125,-123,-121,-119,-116,
 -114,-110,-107,-103,-99,-95,-90,-85,-80,-75,
 -69,-63,-58,-52,-45,-39,-33,-26,-20,-13,-6
};

/*@
  lemma lem2:	\forall integer x,y,z;	0 < x && 0 <= y < z		==> (x<<y) < (x<<z);
  lemma lem2b:	\forall integer x,y,z;	0 <= x && 0 <= z < y		==> (x>>y) < (x>>z);
  lemma lem2c:	\forall integer x,y,z;	0 <= x <= y && 0 <= z		==> (x>>z) <= (y>>z);
  lemma lem2d:	\forall integer x,y,z;	x < (1<<y) && 0 <= z <= y	==> (x>>z) < (1<<(y-z));
  lemma lem3:	\forall integer x,y,z;	0 <= x < (1<<y) && 0 <= y	==> (x<<1)+1 < (1<<(y+1));
  lemma lem4:	\forall integer x;	0 <= x				==> (1<<x) / 2 == 1<<(x-1);
  lemma lem4b:	\forall integer x,y;	0 <= x < y			==> (1<<x)>>y == 0;
  lemma lem5:	\forall integer x,y;	0 <= x && 0 <= y		==> (1<<(x+y)) == (1<<x) * (1<<y);
  lemma lem5b:	\forall integer x,y;	0 <= y <= x			==> (1<<x) == (1<<y) * (1<<(x-y));
  lemma lem6:	\forall integer x;	0 <= x <= 32767			==> 0 <= (x<<1) <= 65534;
  lemma lem7:	\forall integer x,y,z;	0 <= x && 0 <= z <= y		==> (x<<y)>>z == x << (y-z);
*/

/*@
  requires nu < 16;
  assigns \nothing;
  ensures bitrev: a: \result < (1<<nu);
*/
static uint16_t bitrev(uint16_t j, uint16_t nu)
{
  //@ ghost uint16_t const nu_old = nu;
  uint16_t k;
  k = 0;
  /*@
    loop invariant bitrev: b: 0 <= nu <= nu_old < 16;
    loop invariant bitrev: c: k < (1<<(nu_old-nu));
    loop assigns bitrev: d: nu, k, j;
    loop variant nu;
  */
  for (; nu > 0; nu--) {
    k  = (k << 1) + (j & 1);
    //@ assert bitrev: f: k < (1<<(nu_old-nu+1));
    j = j >> 1;
  }
  return k;
}


/* Non interpolating sine... which takes an angle of 0 - 999 */
/*@
  requires \valid_read(&SIN_TAB + (0 .. SIN_TAB_LEN-1));
  requires \forall integer j; 0<=j<SIN_TAB_LEN ==> -127<=SIN_TAB[j]<=+127;
  assigns  \nothing;
  ensures  -127 <= \result <= +127;
*/
static int16_t sinI(uint16_t angleMilli)
{
  uint16_t pos;
  pos = (uint16_t) ((SIN_TAB_LEN * (uint32_t) angleMilli) / 1000);
  return SIN_TAB[pos % SIN_TAB_LEN];
}

/*@
  requires \valid_read(&SIN_TAB + (0 .. SIN_TAB_LEN-1));
  requires \forall integer j; 0<=j<SIN_TAB_LEN ==> -127<=SIN_TAB[j]<=+127;
  assigns  \nothing;
  ensures  -127 <= \result <= +127;
*/
static int16_t cosI(uint16_t angleMilli)
{
  return sinI(angleMilli + 250);
}

/*@
  behavior general:	// minimal contract of ilog2 itself
    requires val < 1<<16;
    assigns  \nothing;
    ensures  ilog2: c: 0 <= \result <= 15;
  behavior pow2:	// special case when val is a power of two; needed for ifft()
    assumes \exists integer i; 0 <= i && val == (1<<i);
    requires val < 1<<16;
    assigns  \nothing;
    ensures ilog2: C: 0 <= \result <= 15;
    ensures ilog2: F: val == (1<<\result);
*/
static uint16_t ilog2(uint16_t val)
{
  uint16_t log;
  //@ ghost uint16_t const VAL = val;
  log = 0;
  val = val >> 1; /* The 20 = 1 => log = 0 => val = 0 */
  /*@
    for general:
      loop invariant ilog2: a: 0 <= log <= 15;
      loop invariant ilog2: b: 0 <= val < (1<<(16-log));
    for pow2:
      loop invariant ilog2: a2: 0 <= log <= 15;
      loop invariant ilog2: A: val == (VAL >> (log+1));
      loop invariant ilog2: B: 0   <  (VAL >>  log   );
    for general:
      loop assigns ilog2: val, log;
    for pow2:
      loop assigns ilog2: val, log;
    // for general,pow2:
      loop variant ilog2: 16-log;
  */
  while (val > 0) {
    //@ for general: assert ilog2: g: val < (1<<(16-log));
    //@ for pow2:    assert ilog2: h: val == (VAL >> (log+1));
    val = val >> 1;
    //@ for general: assert ilog2: e: val < (1<<(16-log-1));
    //@ for pow2:    assert ilog2: i: val == (VAL >> (log+2));
    log++;
  }
  //@ for pow2: assert ilog2: g: val == (VAL >> (log+1));
  return log;
}


/* ifft(xre[], n) - integer (fixpoint) version of Fast Fourier Transform
   An integer version of FFT that takes in-samples in an int16_t array
   and does an fft on n samples in the array.
   The result of the FFT is stored in the same array as the samples
   was stored. Them imaginary part of the result is stored in xim which
   needs to be of the same size as xre (e.g. n ints).

   Note: This fft is designed to be used with 8 bit values (e.g. not
   16 bit values). The reason for the int16_t array is for keeping some
   'room' for the calculations. It is also designed for doing fairly small
   FFT:s since to large sample arrays might cause it to overflow during
   calculations.
*/
/*@
  requires \exists integer b; 1 <= b && n == (1<<b);
  requires \valid(xre+(0..n-1));
  requires \valid(xim+(0..n-1));
  requires \forall integer j; 0<=j<n ==> -128<=xre[j]<+128;
  requires \forall integer j; 0<=j<n ==> -128<=xim[j]<+128;
  requires \forall integer j; 0<=j<SIN_TAB_LEN ==> -127<=SIN_TAB[j]<=+127;
  assigns  *(xre+(0..n-1));
  assigns  *(xim+(0..n-1));
*/
void
ifft(int16_t xre[], int16_t xim[], uint16_t n)
{
  uint16_t nu;
  uint16_t n2;
  uint16_t nu1;
  int p, k, l, i;
  int32_t c, s, tr, ti;

  //  assert ifft1: g: \exists integer b; 1 <= b && n == (1<<b);
  nu = ilog2(n);
  //@ assert ifft1: f2: 1 <= nu <= 15;
  //@ assert ifft1: f: n == (1<<nu);
  nu1 = nu - 1;
  n2 = n / 2;
  //@ assert ifft1: a2: 0 <= nu1 <= 14;
  //@ assert ifft1: a:                            n==(1<<nu) && n2==(1<<nu1);
  //@ assert ifft1: b: n == (1<<(nu-nu1)) * n2;
  //  assert ifft1: b: \exists integer b; 1<=b && n==(1<<b ) && n2==(1<<(b-1));

  // XXX follows immediately from ifft1:b by lem5b,
  // XXX but can't be proven by alt-ergo, cvc4, eprover, spass, z3
  //  assert ifft1: c: n == (1<<1) * n2;

  /*@
    loop invariant ifft1: d: 0 <= i <= n;
    //loop invariant ifft2_n2_nu1: w2: 0 <= nu1 <= 14;
    //loop invariant ifft2_n2_nu1: w: n2 == (1<<nu1);
    loop invariant ifft2: pB: \forall integer j; 0<=j<n ==> -128<=xre[j]<+128;
    loop invariant ifft2: pC: \forall integer j; 0<=j<i ==> xim[j]==0;
    loop assigns i;
    loop assigns   ifft1: e: *(xim+(0..n-1));
    loop variant n-i;
  */
  for (i = 0; i < n; i++)
    xim[i] = 0;

  /*@
    loop invariant ifft2_n_n2: a: n2 < n;
    loop invariant ifft2: b: 1 <= l <= nu+1;
    loop invariant ifft2_n2_nu1: c2: nu1 + l == nu || (nu1==65535 && l-1==nu);
    loop invariant ifft2_n2_nu1: c: n2 == (1<<nu1) || nu1==65535;
    loop invariant ifft2_n2_nu1: c3: 0 <= nu1 <= 14 || nu1==65535;
    loop invariant ifft2_n_n2: d: n == (1<<(nu-nu1)) * n2 || nu1==65535;
    loop invariant ifft2: p9: \forall integer j; 0<=j<n ==> -128<=xre[j]<+128;
    loop invariant ifft2: pA: \forall integer j; 0<=j<n ==> -128<=xim[j]<+128;
    loop assigns l, k, i, p, c, s, tr, ti, nu1, n2;
    loop assigns *(xre+(0..n-1));
    loop assigns *(xim+(0..n-1));
    loop variant nu-l;
  */
  for (l = 1; l <= nu; l++) {
    //@ ghost int kn2 = 0;

    /*@
      loop invariant ifft2_n_n2: e: n2 < n;
      loop invariant ifft2: f: 0 <= k <= n;
      loop invariant ifft2: g: k == kn2 * n2;
      loop invariant ifft2_n_n2: h: n == (1<<(nu-nu1)) * n2;
      loop invariant ifft2_n2_nu1: i2: nu1 + l == nu;
      loop invariant ifft2_n2_nu1: i: n2 == (1<<nu1);
      loop invariant ifft2_n2_nu1: i3: 0 <= nu1 <= 14;
      loop invariant ifft2: p7: \forall integer j; 0<=j<n ==> -128<=xre[j]<+128;
      loop invariant ifft2: p8: \forall integer j; 0<=j<n ==> -128<=xim[j]<+128;
      loop assigns k, i, p, c, s, tr, ti;
      loop assigns *(xre+(0..n-1));
      loop assigns *(xim+(0..n-1));
      loop variant n-k;
    */
    for (k = 0; k < n; k += n2) {
      //@ ghost int const k_old = k;
      //@ assert ifft2_k_n_n2: j: k <= n-n2;

      /*@
	loop invariant ifft2: k: 1 <= i <= n2+1 <= n;
	loop invariant ifft2_k_n_n2: l: 0 <= k;
	loop invariant ifft2_k_n_n2: m:      k <= n;
	loop invariant ifft2: n:  k == k_old + i - 1;
	loop invariant ifft2: n2: k_old == kn2 * n2;
	loop invariant ifft2_n2_nu1: o2: nu1 + l == nu;
	loop invariant ifft2_n2_nu1: o: n2 == (1<<nu1);
	loop invariant ifft2_n2_nu1: o3: 0 <= nu1 <= 14;
	// proof about preserving p5,p6 needs some tricky trigonometric argument:
	loop invariant ifft2: p5: \forall integer j; 0<=j<n ==> -128<=xre[j]<+128;
	loop invariant ifft2: p6: \forall integer j; 0<=j<n ==> -128<=xim[j]<+128;
	loop assigns k, i, p, c, s, tr, ti;
	loop assigns *(xre+(0..n-1));
	loop assigns *(xim+(0..n-1));
	loop variant n2-i;
      */
      for (i = 1; i <= n2; i++) {
	p = bitrev(k >> nu1, nu);
	c = cosI((1000 * p) / n);
	s = sinI((1000 * p) / n);

	//@ assert ifft2: p1: \forall integer j; 0<=j<n ==> -128<=xre[j]<+128;
	//@ assert ifft2: p2: \forall integer j; 0<=j<n ==> -128<=xim[j]<+128;
	//@ assert ifft2: p3: -128<=c<+128;
	//@ assert ifft2: p4: -128<=s<+128;
	tr = ((xre[k + n2] * c + xim[k + n2] * s) >> RESOLUTION);
	ti = ((xim[k + n2] * c - xre[k + n2] * s) >> RESOLUTION);
	// proof p,q needs some tricky trigonometric argument:
	//@ assert ifft2: p: -(65535>>RESOLUTION) <= tr <= 65535>>RESOLUTION;
	//@ assert ifft2: q: -(65535>>RESOLUTION) <= ti <= 65535>>RESOLUTION;

	xre[k + n2] = xre[k] - tr;
	xim[k + n2] = xim[k] - ti;
	xre[k] += tr;
	xim[k] += ti;
	k++;
      }
      //@ assert ifft2: r: k == k_old + n2;
      //@ ghost kn2 += 2;
      //@ assert ifft2: m2: k <= n - n2 || k==n;
    }
    //@ ghost uint16_t const nu1_old = nu1;
    //@ assert ifft2_n2_nu1: u: n2 == (1<<nu1);
    //@ assert ifft2_n2_nu1: u2: 0 <= nu1 <= 14;
    //@ assert ifft2_n2_nu1: u3: nu1 + l == nu;
    nu1--;
    //@ assert ifft2_n2_nu1: x4: nu1_old == 0 ==> nu1 == 65535;	// hint provers at case-distinction
    //@ assert ifft2_n2_nu1: x: n2 == (1<<(nu1+1)) || nu1==65535;
    //@ assert ifft2_n2_nu1: x2: 0 <= nu1 <= 14 || nu1==65535;
    //@ assert ifft2_n2_nu1: x3: nu1 + 1 + l == nu || nu1==65535;
    //@ assert ifft2_n_n2: t1: n == (1<<(nu-nu1-1)) * n2 || nu1==65535;
    n2 = n2 / 2;
    //@ assert ifft2_n_n2: t: n == (1<<(nu-nu1)) * n2 || nu1==65535;
    //@ assert ifft2_n2_nu1: v: n2 == (1<<nu1) || nu1==65535;
  }

  /*@
    loop invariant ifft3: a: 0 <= k <= n;
    loop assigns k, p, n2;
    loop assigns *(xre+(0..n-1));
    loop assigns *(xim+(0..n-1));
    loop variant n-k;
  */
  for (k = 0; k < n; k++) {
    p = bitrev(k, nu);
    //@ assert ifft3: b: 0 <= p <= n;
    if (p > k) {
      n2 = xre[k];
      xre[k] = xre[p];
      xre[p] = n2;

      n2 = xim[k];
      xim[k] = xim[p];
      xim[p] = n2;
    }
  }

  /* This is a fast but not 100% correct magnitude calculation */
  /* Should be sqrt(xre[i]^2 + xim[i]^2) and normalized with div. by n */
  /*@
    loop invariant ifft4: a: 0 <= i <= n2 < n;
    loop assigns i;
    loop assigns *(xre+(0..n-1));
    loop variant n2-i;
  */
  for (i = 0, n2 = n / 2; i < n2; i++) {
    xre[i] = (ABS(xre[i]) + ABS(xim[i]));
  }

  // XXX poor man's check for consistency of lemmas -
  // XXX don't move it up in the file
  //@ assert check: \false;
}
