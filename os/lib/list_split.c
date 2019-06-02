#ifndef LIST_SPLIT_C
#define LIST_SPLIT_C
/*
 * Copyright (c) 2018, Inria, CEA, Northern Arizona University.
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
 * This file is part of the verification of the Contiki operating system.
 *
 * Authors: - Allan Blanchard <mail@allan-blanchard.fr>
 *          - Nikolai Kosmatov <nikolai.kosmatov@cea.fr>
 *          - Frédéric Loulergue <frederic.loulergue@nau.edu>
 */

/*@ requires \valid(list);
  @ requires linked_ll(*list, end, to_logic_list(*list, end));
  @ requires \length(to_logic_list(*list, end)) < INT_MAX ;
  @ requires in_list(sep, to_logic_list(*list, end)) || 
  @          ptr_separated_from_list(sep, to_logic_list(*list, end)) ;
  @
  @ assigns \nothing ;
  @
  @ behavior contains:
  @   assumes in_list(sep, to_logic_list(*list, end)) ;
  @   ensures to_logic_list(*list, end) == 
  @          (to_logic_list(*list, sep) ^ to_logic_list(sep, end));
  @   ensures linked_ll(*list, sep, to_logic_list(*list, sep));
  @   ensures linked_ll(sep, end, to_logic_list(sep, end));
  @
  @ behavior does_not_contain:
  @   assumes !in_list(sep, to_logic_list(*list, end)) ;
  @ 
  @ complete behaviors ;
  @ disjoint behaviors ;
  @*/
void
list_split(list_t list, struct list *sep, struct list *end)
{
  if(*list == end){
    //@ assert !in_list(sep, to_logic_list(*list, end)) ;
    return ;
  }
  if(*list == sep){
    //@ assert linked_ll(*list, sep, to_logic_list(*list, sep));
    return ;
  }
  
  struct list* l = *list ; 
  int n = 0 ;
  /*@ loop invariant \nth(to_logic_list(*list, end), n) == l ;
    @ loop invariant n == \length(to_logic_list(*list, l)) ;
    @ loop invariant linked_ll(*list, end, to_logic_list(*list, end));
    @ loop invariant linked_ll(*list, l, to_logic_list(*list, l));
    @ loop invariant linked_ll(l, end, to_logic_list(l, end));
    @ loop invariant 0 <= n < \length(to_logic_list(*list, end)) ;
    @ loop invariant 
      ptr_separated_from_list(sep, to_logic_list(*list, end)) ||
      \exists integer x ; \nth(to_logic_list(*list, end), x) == sep 
                       && n < x < \length(to_logic_list(*list, end)) ;
    @ loop assigns l, n ;
    @ loop variant \length(to_logic_list(l, end)); 
    @*/
  while(l->next != sep && l->next != end){
    //@ assert in_list(l->next, to_logic_list(*list, end)) || l->next == end ;
    //@ assert to_logic_list(*list, end) == (to_logic_list(*list, l) ^ to_logic_list(l, end)) ;
    /*@ assert \forall integer i ; 0 <= i < \length(to_logic_list(*list, l)) ==>
        \nth(to_logic_list(*list, end), i) == \nth(to_logic_list(*list, l), i) ;
    */
    /*@ assert \forall integer i ; 0 <= i < \length(to_logic_list(*list, l)) ==>
        \separated(\nth(to_logic_list(*list, l), i),
	           \nth(to_logic_list(*list, end), \length(to_logic_list(*list, l))+1));
    */
    //@ assert \nth(to_logic_list(*list, end), n+1) == l->next || l->next == end ;
    /*@ assert \nth(to_logic_list(*list, end), \length(to_logic_list(*list, l))+1) == l->next ||
        l->next == end ;
    */    
    //@ assert ptr_separated_from_list(l->next, to_logic_list(*list, l)) ;
    //@ assert to_logic_list(*list, l->next) == (to_logic_list(*list, l) ^ [| l |]) ;
    
    l = l->next ;
    ++n;
  }

  //@ assert in_list(l->next, to_logic_list(*list, end)) || l->next == end ;
  //@ assert in_list(l->next, to_logic_list(*list, end)) ==> l->next == sep ;
  //@ assert !in_list(sep, to_logic_list(*list, end)) ==> l->next == end;
  //@ assert linked_ll(*list, l->next, to_logic_list(*list, l->next));
}

#endif /*LIST_SPLIT*/
