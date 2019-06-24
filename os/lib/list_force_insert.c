#ifndef LIST_FORCE_INSERT_C
#define LIST_FORCE_INSERT_C
/*
 * Copyright (c) 2004, Swedish Institute of Computer Science.
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
 * Authors: - Adam Dunkels <adam@sics.se>
 *          - Allan Blanchard <mail@allan-blanchard.fr>
 *          - Nikolai Kosmatov <nikolai.kosmatov@cea.fr>
 *          - Frédéric Loulergue <frederic.loulergue@nau.edu>
 */

/*@ requires ValidHandler: \valid(list);
  @ requires HandlerSep:   dptr_separated_from_list(list, to_logic_list(*list, NULL));
  @ requires Linked:        linked_ll(*list, NULL, to_logic_list(*list, NULL));
  @ requires LengthMax:    \length(to_logic_list(*list, NULL)) < INT_MAX ;
  @ requires \valid(item) && \valid(prev) ;
  @ requires in_list(prev, to_logic_list(*list, NULL)) ;
  @ requires ptr_separated_from_list(item, to_logic_list(*list, NULL)) ;
  @ requires \separated(list, prev, item) ;
  @
  @ ensures HandlerSep:    dptr_separated_from_list(list, to_logic_list(*list, NULL));
  @ ensures ValidHandler:  \valid(list);
  @ ensures Linked:         linked_ll(*list, NULL, to_logic_list(*list, NULL));
  @ ensures NewList: to_logic_list(*list, NULL) ==
  @                  (to_logic_list{Pre}(\old(*list), \old(prev->next)) ^
  @                  [| item |] ^
  @                  to_logic_list{Pre}(\old(prev->next), NULL)) ;
  @ ensures SizeInc: \length(to_logic_list(*list, NULL)) == 
  @                  \length(to_logic_list{Pre}(\at(*list,Pre), NULL)) + 1 ;
  @
  @ assigns item->next, prev->next ;
  @*/
void
list_force_insert(list_t list, struct list *prev, struct list *item)
{
  //@ assert prev->next == NULL || in_list(prev->next, to_logic_list(*list, NULL)) ;
  //@ ghost list_split(list, prev, NULL);
  //@ ghost list_split(list, prev->next, NULL);

  //@ ghost L1: ;
  
  /*@ assert SepReformulation_Left: \let ll = to_logic_list(*list, prev->next) ;
    \forall integer i ; 0 <= i < \length(ll) ==> \separated(\nth(ll, i), item) ;
  */  
  /*@ assert SepReformulation_Right: \let ll = to_logic_list(prev->next, NULL) ;
    \forall integer i ; 0 <= i < \length(ll) ==> \separated(\nth(ll, i), item) ;
  */

  /*@ assigns \nothing ;
    ensures all_separated_in_list(
      to_logic_list(\at(*list, L1), \at(prev->next, L1)) ^ 
      [| item |] ^ 
      to_logic_list(\at(prev->next, L1), NULL)
    ) ;
  */{
    //@ assert all_separated_in_list(to_logic_list(*list, NULL)) ;
    /*@ assert all_separated_in_list(
        to_logic_list(*list, prev->next) ^ to_logic_list(prev->next, NULL)) ;
    */
    /*@ assert ptr_separated_from_list(item,
        to_logic_list(*list, prev->next) ^ to_logic_list(prev->next, NULL)) ;
    */
  }

  item->next = prev->next;
  //@ ghost L2: ; 

  //@ assert \at(*list, L2) == \at(*list, L1) ;
  //@ assert \at(prev->next, L2) == \at(prev->next, L1) ;

  // GHOST :
  /*@ assigns \nothing ;
    ensures linked_ll(\at(*list, L2), \at(prev->next, L2), 
                   to_logic_list{L2}(\at(*list, L2), \at(prev->next, L2)));
    ensures to_logic_list{L2}(\at(*list, L2), \at(prev->next, L2)) == 
            to_logic_list{L1}(\at(*list, L1), \at(prev->next, L1)) ;
    ensures dptr_separated_from_list(list, to_logic_list{L2}(\at(*list, L2), \at(prev->next, L2)));
  */ {
    //@ assert linked_ll{L1}(\at(*list,L1), prev->next, to_logic_list{L1}(\at(*list,L1), prev->next));
    //@ assert unchanged{L1, Here}(to_logic_list{L1}(*list, prev->next)) ;
  }

  /*@ assigns \nothing ;
    ensures linked_ll{L2}(item, NULL, to_logic_list{L2}(item, NULL)) ;
    ensures to_logic_list{L2}(item, NULL) == 
            ([| item |] ^ to_logic_list{L1}(\at(prev->next, L1), NULL));
    ensures dptr_separated_from_list(list, to_logic_list{L2}(item, NULL));
  */ {
    if(item->next == NULL){
      //@ assert to_logic_list(item, NULL) == [| item |] ;
      //@ assert linked_ll(item, NULL, [| item |]) ;
    } else {
      //@ assert linked_ll{L1}(prev->next, NULL, to_logic_list{L1}(prev->next, NULL)) ;
      //@ assert unchanged{L1, Here}(to_logic_list{L1}(prev->next, NULL)) ;
      //@ assert ptr_separated_from_list(item, to_logic_list{L1}(prev->next, NULL)) ;
    }
  }

  //@ assert to_logic_list{L2}(*list, prev->next) == (to_logic_list{L2}(*list, prev) ^ [| prev |]) ;

  /*@ assigns \nothing ;
      ensures \let ll = to_logic_list{L2}(\at(*list, L2), prev) ;
      \forall integer i ; 0 <= i < \length(ll) ==> \separated(\nth(ll, i), prev) ;
  */ {
    /*@ assert \let ll = to_logic_list{L2}(*list, prev) ;
      \forall integer i ; 0 <= i < \length(ll) ==>
      \nth(ll, i) == \nth(to_logic_list{L2}(*list, prev->next), i) ;
    */
    //@ assert \let ll = to_logic_list{L2}(*list, prev) ^ [|prev|] ; \nth(ll, \length(ll)-1) == prev ;
    /*@ assert \let ll = to_logic_list{L2}(*list, prev->next) ;
      \forall integer i ; 0 <= i < \length(ll) - 1 ==> \separated(\nth(ll, i), prev);
    */
  }

  /*@ assigns \nothing ;
      ensures \let ll = to_logic_list{L2}(\at(prev->next, L2), NULL) ;
      \forall integer i ; 0 <= i < \length(ll) ==> \separated(\nth(ll, i), prev) ;
  */ {
    //@ assert linked_ll(prev, NULL, to_logic_list(prev, NULL)) ;
    //@ assert linked_ll(prev->next, NULL, to_logic_list(prev->next, NULL)) ;
    //@ assert ptr_separated_from_list(prev, to_logic_list(prev->next, NULL)) ;
  }
  //@ assert \separated(prev, item) ;
  
  prev->next = item;
  //@ ghost L3: ;
  
  /*@ assigns \nothing ;
    ensures linked_ll{L3}(item, NULL, to_logic_list{L3}(item, NULL)) ;
    ensures to_logic_list{L3}(item, NULL) == 
            ([| item |] ^ to_logic_list{L1}(\at(prev->next, L1), NULL));
    ensures dptr_separated_from_list(list, to_logic_list{L3}(item, NULL));
  */ {
    //@ assert linked_ll{L2}(\at(prev->next, L2), NULL, to_logic_list{L2}(\at(prev->next, L2), NULL));
    //@ assert unchanged{L2, L3}(to_logic_list{L2}(\at(prev->next, L2), NULL));
    //@ assert unchanged{L2, L3}([| item |]);
    //@ assert unchanged{L2, L3}(to_logic_list{L2}(item, NULL));
  }

  /*@ assigns \nothing ;
    ensures linked_ll{L3}(\at(*list, L3), prev, to_logic_list{L3}(\at(*list, L3), prev)) ;
    ensures to_logic_list{L3}(*list, prev) == to_logic_list{L1}(\at(*list, L1), prev) ;
  */ {
    //@ assert linked_ll{L2}(*list, prev, to_logic_list{L2}(*list, prev)) ;
    //@ assert unchanged{L2, L3}(to_logic_list{L2}(*list, prev)) ;
  }

  /*@ assigns \nothing ;
    ensures linked_ll{L3}(\at(*list, L3), item, to_logic_list{L3}(\at(*list, L3), item)) ;
    ensures to_logic_list{L3}(\at(*list, L3), item) == 
            to_logic_list{L1}(\at(*list, L1), \at(prev->next, L1)) ;
  */ {
    //@ assert ptr_separated_from_list(item, to_logic_list{L3}(*list, prev)) ;
    //@ assert to_logic_list{L3}(*list, item) == (to_logic_list{L1}(*list, prev) ^ [| prev |]) ;
  }

  //@ assert item == \at(item, L1);
  //@ assert prev == \at(prev, L1);
  
  /*@ assigns \nothing ;
    ensures linked_ll{L3}(\at(*list, L3), NULL, to_logic_list{L3}(*list, NULL)) ;
    ensures to_logic_list{L3}(\at(*list, L3), NULL) ==
            (to_logic_list{L1}(\at(*list, L1), \at(prev->next, L1)) ^
	    [| item |] ^ to_logic_list{L1}(\at(prev->next, L1), NULL)) ;
  */ {
    //@ assert linked_ll(*list, item, to_logic_list{L3}(*list, item)) ;
    //@ assert all_separated_in_list(to_logic_list{L3}(*list, item) ^ to_logic_list{L3}(item, NULL)) ;
    //@ assert ptr_separated_from_list(NULL, to_logic_list{L3}(*list, item)) ;
    /*@ assert to_logic_list{L3}(\at(*list, L3), NULL) ==
              (to_logic_list{L3}(\at(*list, L3), item) ^ to_logic_list{L3}(item, NULL)) ;
    */
  }
}

#endif /*LIST_FORCE_INSERT_C*/
