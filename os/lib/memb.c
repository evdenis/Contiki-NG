/*
 * Copyright (c) 2004, Swedish Institute of Computer Science.
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
 * Author: Adam Dunkels <adam@sics.se>
 *
 */

/**
 * \addtogroup memb
 * @{
 */

 /**
 * \file
 * Memory block allocation routines.
 * \author Adam Dunkels <adam@sics.se>
 */
#include <string.h>

#include "contiki.h"
#include "lib/memb.h"

/*---------------------------------------------------------------------------*/
void
memb_init(struct memb *m)
{
  memset(m->count, 0, m->num);
  memset(m->mem, 0, m->size * m->num);
}
/*---------------------------------------------------------------------------*/
void *
memb_alloc(struct memb *m)
{
  int i;

  /*@
    loop invariant 0 <= i <= m->num;
    loop invariant \forall int j; 0 <= j < i ==> m->count[j] != 0;
    loop assigns i;
    loop variant m->num - i;
  */
  for(i = 0; i < m->num; ++i) {
    //@ ghost occ_a_split(0, m->count, 0, i, m->num);
    //@ ghost occ_a_split(0, m->count, i, i+1, m->num);
    if(m->count[i] == 0) {
      /* If this block was unused, we increase the reference count to
	 indicate that it now is used and return a pointer to the
	 memory block. */
      //@ assert occ_a{Here}(0, m->count, i, i+1) == 1;
      //@ ghost BeforeAlloc:
      ++(m->count[i]);

      //@ ghost same_elems_means_same_occ(BeforeAlloc, Here, 0, m->count, 0, i) ;
      //@ ghost same_elems_means_same_occ(BeforeAlloc, Here, 0, m->count, i+1, m->num) ;
     
      //@ assert occ_a{Here}(0, m->count, i, i+1) == 0;
      //@ assert occ_a{Here}(0, m->count, i, i+1) == occ_a{BeforeAlloc}(0, m->count, i, i+1) - 1;

      //@ ghost occ_a_split(0, m->count, 0, i, m->num);
      //@ ghost occ_a_split(0, m->count, i, i+1, m->num);

      /*@ assert 0 <= i * m->size <= (m->num - 1) * m->size; */
      return (void *)((char *)m->mem + (i * m->size));
    }
  }

  /* No free block was found, so we return NULL to indicate failure to
     allocate block. */
  return NULL;
}
/*---------------------------------------------------------------------------*/
char
memb_free(struct memb *m, void *ptr)
{
  int i;
  char *ptr2;

  /* Walk through the list of blocks and try to find the block to
     which the pointer "ptr" points to. */
  ptr2 = (char *)m->mem;
  /*@
    loop invariant 0 <= i <= m->num;
    loop invariant valid_memb(m);
    loop invariant ptr2 == _memb_ptr(m, i);
    loop invariant i == _memb_index(m, _memb_ptr(m, i));
    loop invariant \forall int j; 0 <= j < i ==> (char*) ptr != (char*) m->mem + (j * m->size);
    loop assigns i, ptr2;
    loop variant m->num - i;
  */
  for(i = 0; i < m->num; ++i) {
    //@ ghost occ_a_split(0, m->count, 0, i, m->num);
    //@ ghost occ_a_split(0, m->count, i, i+1, m->num);
    if(ptr2 == (char *)ptr) {
      /* We've found to block to which "ptr" points so we decrease the
	 reference count and return the new value of it. */
      //@ ghost Before:

      if(m->count[i] > 0) {
	/* Make sure that we don't deallocate free memory. */
	--(m->count[i]);
      }
      
      //@ ghost same_elems_means_same_occ(Before, Here, 0, m->count, 0, i) ;
      //@ ghost same_elems_means_same_occ(Before, Here, 0, m->count, i+1, m->num) ;
      
      //@ ghost occ_a_split(0, m->count, 0, i, m->num);
      //@ ghost occ_a_split(0, m->count, i, i+1, m->num);
      return m->count[i];
    }
    ptr2 += m->size;
  }
  return -1;
}
/*---------------------------------------------------------------------------*/
int
memb_inmemb(struct memb *m, void *ptr)
{
  return (char *)ptr >= (char *)m->mem &&
    (char *)ptr < (char *)m->mem + (m->num * m->size);
}
/*---------------------------------------------------------------------------*/
int
memb_numfree(struct memb *m)
{
  int i;
  int num_free = 0;

  /*@
    loop invariant 0 <= i <= m->num;
    loop invariant num_free <= i;
    loop invariant num_free == occ_a(0, m->count, 0, i);
    loop assigns i, num_free;
    loop variant m->num - i;
  */
  for(i = 0; i < m->num; ++i) {
    if(m->count[i] == 0) {
      ++num_free;
    }
  }

  return num_free;
}
/** @} */
