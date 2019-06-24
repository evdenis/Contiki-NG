/*
 * Copyright (c) 2013, Hasso-Plattner-Institut.
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
 * This file is part of the Contiki operating system.
 *
 */

/**
 * \file
 *         AES_128-based CCM* implementation.
 * \author
 *         Original: Konrad Krentz <konrad.krentz@gmail.com>
 *         Generified version: Justin King-Lacroix <justin.kinglacroix@gmail.com>
 */

#include "ccm-star.h"
#include "lib/aes-128.h"
#include <string.h>

/* see RFC 3610 */
#define CCM_STAR_AUTH_FLAGS(Adata, M) ((Adata ? (1u << 6) : 0) | (((M - 2u) >> 1) << 3) | 1u)
#define CCM_STAR_ENCRYPTION_FLAGS     1

/*---------------------------------------------------------------------------*/
/*@
   logic integer limit_m(uint8_t m_len, uint8_t pos) =
     0 <= m_len - pos < AES_128_BLOCK_SIZE ? m_len : (AES_128_BLOCK_SIZE + pos);
 
   logic integer limit_a_len(uint8_t a_len) =
     0 <= a_len < AES_128_BLOCK_SIZE - 2 ? a_len + 2 : AES_128_BLOCK_SIZE;

   logic integer limit_a_pos(uint8_t a_len, uint8_t pos) =
     0 <= a_len - pos < AES_128_BLOCK_SIZE ? a_len - pos : AES_128_BLOCK_SIZE;

   logic integer limit_a_while(uint8_t a_len) =
     0 <= a_len < AES_128_BLOCK_SIZE + 14 ? a_len : AES_128_BLOCK_SIZE;

   logic integer limit_pos(uint8_t pos) =
     0 <= 30 - pos < AES_128_BLOCK_SIZE ? 30 - pos : AES_128_BLOCK_SIZE;

   predicate valid_read_a{L0}(uint8_t *a, uint8_t a_len) =
     a_len > 0 ? \valid_read(a+ (0 .. (a_len - 1))) : \at(a, L0) == NULL;

   predicate valid_m{L0}(uint8_t *m, uint8_t m_len) =
     m_len > 0 ? \valid(m+ (0 .. (m_len - 1))) : \at(m, L0) == NULL;
     
   predicate valid_read_m{L0}(uint8_t *m, uint8_t m_len) =
     m_len > 0 ? \valid_read(m+ (0 .. (m_len - 1))) : \at(m, L0) == NULL;
*/

/*@
  requires \valid(iv+ (0 .. 15)) 
  && \valid_read(nonce+ (0 .. (CCM_STAR_NONCE_LENGTH - 1))) 
  && CCM_STAR_NONCE_LENGTH == 13;
  requires \separated(iv+(0 .. 15), nonce+(0 .. (CCM_STAR_NONCE_LENGTH - 1)));
  ensures \at(iv[0],Post) == flags && \at(iv[14],Post) == 0 && \at(iv[15],Post) == counter;
  //ensures \forall integer i; 0 <= i < CCM_STAR_NONCE_LENGTH ==> \at(iv[i+1],Post) == \at(nonce[i],Pre);
  assigns iv[0 .. 15];
*/
static void
set_iv(uint8_t *iv,
    uint8_t flags,
    const uint8_t *nonce,
    uint8_t counter)
{
  /*@ assert \valid(iv+ (0 .. 15)) && \valid_read(nonce+ (0 .. (CCM_STAR_NONCE_LENGTH - 1)));*/
  iv[0] = flags;
  memcpy(iv + 1, nonce, CCM_STAR_NONCE_LENGTH);
  iv[14] = 0;
  iv[15] = counter;
}
/*---------------------------------------------------------------------------*/
/* XORs the block m[pos] ... m[pos + 15] with K_{counter} */
/*@
  requires 0 < m_len;
  requires 0 <= pos <= m_len;
  requires \valid(m_and_result+ (pos .. (limit_m(m_len, pos) - 1))); 
  requires \valid_read(nonce+ (0 .. (CCM_STAR_NONCE_LENGTH - 1)));
  assigns m_and_result[pos .. (limit_m(m_len, pos) - 1)];
*/
static void
ctr_step(const uint8_t *nonce,
    uint8_t pos,
    uint8_t *m_and_result,
    uint8_t m_len,
    uint8_t counter)
{
  uint8_t a[AES_128_BLOCK_SIZE];
  uint8_t i;
  
  /*@ assert \valid(a+(0..(AES_128_BLOCK_SIZE-1))); */
  set_iv(a, CCM_STAR_ENCRYPTION_FLAGS, nonce, counter);
  AES_128.encrypt(a);
  /*@
    loop invariant 0 <= i <= AES_128_BLOCK_SIZE;
    loop assigns i, m_and_result[pos .. (limit_m(m_len, pos) - 1)];
    loop variant AES_128_BLOCK_SIZE - i;
  */
  for(i = 0; (pos + i < m_len) && (i < AES_128_BLOCK_SIZE); i++) {
    m_and_result[pos + i] ^= a[i];
  }
}
/*---------------------------------------------------------------------------*/
/*@
  requires 0 <= a_len && 0 <= m_len;
  requires valid_read_m{Pre}(m, m_len);
  requires \valid_read(nonce+ (0 .. (CCM_STAR_NONCE_LENGTH - 1))); 
  requires valid_read_a{Pre}(a, a_len);
  requires mic_len <= AES_128_BLOCK_SIZE; 
  assigns result[0 .. (mic_len - 1)];
*/
static void
mic(const uint8_t *nonce,
    const uint8_t *m, uint8_t m_len,
    const uint8_t *a, uint8_t a_len,
    uint8_t *result,
    uint8_t mic_len)
{
  uint8_t x[AES_128_BLOCK_SIZE];
  uint8_t pos;
  uint8_t i;
  
  set_iv(x, CCM_STAR_AUTH_FLAGS(a_len, mic_len), nonce, m_len);
  AES_128.encrypt(x);
  
  if(a_len) {
    x[1] = x[1] ^ a_len;
    /*@
      loop invariant 2 <= i <= limit_a_len(a_len);
      loop assigns x[2 .. (limit_a_len(a_len) - 1)], i;
      loop variant limit_a_len(a_len) - i;
    */
    for(i = 2; (i - 2 < a_len) && (i < AES_128_BLOCK_SIZE); i++) {
      x[i] ^= a[i - 2];
    }
    
    AES_128.encrypt(x);
    
    pos = 14;
    
    /*@
      loop invariant pos <= a_len + AES_128_BLOCK_SIZE;
      loop assigns x[0 .. (AES_128_BLOCK_SIZE - 1)], i, pos;
    */
    while(pos < a_len) {
      /*@
        loop invariant 0 <= i <= limit_a_pos(a_len,pos);
        loop assigns x[0 .. (limit_a_pos(a_len,pos) - 1)], i;
        loop variant limit_a_pos(a_len,pos) - i;
      */
      for(i = 0; (pos + i < a_len) && (i < AES_128_BLOCK_SIZE); i++) {
        x[i] ^= a[pos + i];
      }
      pos += AES_128_BLOCK_SIZE;
      //*@ assert pos % AES_128_BLOCK_SIZE == 14; */
      AES_128.encrypt(x);
    }
  }
  
  if(m_len) {
    pos = 0;
    /*@
      loop invariant pos % AES_128_BLOCK_SIZE == 0;
      loop invariant pos <= 30 + AES_128_BLOCK_SIZE;
      loop assigns x[0 .. (AES_128_BLOCK_SIZE - 1)], i, pos;
    */
    while(pos < m_len) {
      /*@
        loop invariant 0 <= i <= limit_pos(pos);
        loop assigns x[0 .. (limit_pos(pos) - 1)], i;
        loop variant limit_pos(pos) - i;
      */
      for(i = 0; (pos + i < m_len) && (i < AES_128_BLOCK_SIZE); i++) {
        x[i] ^= m[pos + i];
      }
      pos += AES_128_BLOCK_SIZE;
      AES_128.encrypt(x);
    }
  }
  
  ctr_step(nonce, 0, x, AES_128_BLOCK_SIZE, 0);
  
  memcpy(result, x, mic_len);
}
/*---------------------------------------------------------------------------*/
/*@
  requires 0 <= m_len;
  requires valid_m{Pre}(m, m_len); 
  requires \valid_read(nonce+ (0 .. (CCM_STAR_NONCE_LENGTH - 1))); 
  assigns m[0 .. (m_len - 1)];
*/
static void
ctr(const uint8_t *nonce, uint8_t *m, uint8_t m_len)
{
  uint8_t pos;
  uint8_t counter;
  
  pos = 0;
  counter = 1;
  /*@
    loop invariant pos <= m_len + AES_128_BLOCK_SIZE;
    loop assigns m[0 .. (m_len - 1)], pos, counter;
  */
  while(pos < m_len) {
    ctr_step(nonce, pos, m, m_len, counter++);
    pos += AES_128_BLOCK_SIZE;
  }
}
/*---------------------------------------------------------------------------*/
/*@
  requires \valid(key+ (0 .. (AES_128_KEY_LENGTH - 1)));
  assigns \nothing;
*/
static void
set_key(const uint8_t *key)
{
  AES_128.set_key(key);
}
/*---------------------------------------------------------------------------*/
/*@
  requires 0 <= a_len && 0 <= m_len;
  requires valid_m{Pre}(m, m_len); 
  requires \valid(nonce+ (0 .. (CCM_STAR_NONCE_LENGTH - 1)));
  requires valid_read_a{Pre}(a, a_len); 
  requires mic_len <= AES_128_BLOCK_SIZE; 
  assigns m[0 .. (m_len - 1)], result[0 .. (mic_len - 1)];
*/
static void
aead(const uint8_t* nonce,
    uint8_t* m, uint8_t m_len,
    const uint8_t* a, uint8_t a_len,
    uint8_t *result, uint8_t mic_len,
    int forward)
{
  if(!forward) {
    /* decrypt */
    ctr(nonce, m, m_len);
  }
  
  mic(nonce,
    m, m_len,
    a, a_len,
    result,
    mic_len);
  
  if(forward) {
    /* encrypt */
    ctr(nonce, m, m_len);
  }
}
/*---------------------------------------------------------------------------*/
const struct ccm_star_driver ccm_star_driver = {
  set_key,
  aead
};
/*---------------------------------------------------------------------------*/
