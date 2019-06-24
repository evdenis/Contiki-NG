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
 * \file
 * Linked list library implementation.
 *
 * \author Adam Dunkels <adam@sics.se>
 *
 */

/**
 * \addtogroup list
 * @{
 */
#include "contiki.h"
#include "lib/list.h"

#include <string.h>
/*---------------------------------------------------------------------------*/
struct list {
  struct list *next;
};
/*---------------------------------------------------------------------------*/
/**
 * Initialize a list.
 *
 * This function initalizes a list. The list will be empty after this
 * function has been called.
 *
 * \param list The list to be initialized.
 */
void
list_init(list_t list)
{
  *list = NULL;
}
/*---------------------------------------------------------------------------*/
/**
 * Get a pointer to the first element of a list.
 *
 * This function returns a pointer to the first element of the
 * list. The element will \b not be removed from the list.
 *
 * \param list The list.
 * \return A pointer to the first element on the list.
 *
 * \sa list_tail()
 */
void *
list_head(list_t list)
{
  return *list;
}
/*---------------------------------------------------------------------------*/
/**
 * Duplicate a list.
 *
 * This function duplicates a list by copying the list reference, but
 * not the elements.
 *
 * \note This function does \b not copy the elements of the list, but
 * merely duplicates the pointer to the first element of the list.
 *
 * \param dest The destination list.
 * \param src The source list.
 */
void
list_copy(list_t dest, list_t src)
{
  /*@ assert SepDest: 
    \let ll = to_logic_list{Pre}(*src, NULL) ;
    \forall integer i ; 0 <= i < \length(ll) ==> \separated(\nth(ll, i), dest) ;
  */
  *dest = *src;
  //@ assert unchanged{Pre,Here}(to_logic_list{Pre}(*src, NULL)) ;
  //@ assert linked_ll(*src, NULL, to_logic_list(*src, NULL));
}
/*---------------------------------------------------------------------------*/
/**
 * Get the tail of a list.
 *
 * This function returns a pointer to the elements following the first
 * element of a list. No elements are removed by this function.
 *
 * \param list The list
 * \return A pointer to the element after the first element on the list.
 *
 * \sa list_head()
 */
void *
list_tail(list_t list)
{
  struct list *l;

  if(*list == NULL) {
    return NULL;
  }

  /*@ loop invariant \nth(to_logic_list(*list, NULL), n) == l && l != NULL;
    @ loop invariant linked_ll(l, NULL, to_logic_list(l, NULL));
    @ loop invariant linked_ll(*list, NULL, to_logic_list(*list, NULL));
    @ loop invariant n == \length(to_logic_list(*list, NULL)) - 
    @                     \length(to_logic_list(l, NULL));
    @ loop invariant 0 <= n <= \length(to_logic_list(*list, NULL))-1 ;
    @ loop assigns l, n ;
    @ loop variant \length(to_logic_list(l->next, NULL)); 
    @*/
  for(l = *list; l->next != NULL; l = l->next);

  return l;
}
/*---------------------------------------------------------------------------*/
/**
 * Add an item at the end of a list.
 *
 * This function adds an item to the end of the list.
 *
 * \param list The list.
 * \param item A pointer to the item to be added.
 *
 * \sa list_push()
 *
 */
void
list_add(list_t list, void *item)
{
  /*@ assert ! in_list(item, to_logic_list(*list, NULL)) ==>
             (\forall integer n ; 0 <= n < \length(to_logic_list(*list, NULL)) ==> 
                \nth(to_logic_list(*list, NULL), n) != item) ;
  */  
  struct list *l;

  /* Make sure not to add the same element twice */
  list_remove(list, item);
  //@ ghost AR: ;

  /*@ assert SepReformulation: \let ll = to_logic_list{AR}(*list, NULL) ;
      \forall integer i ; 0 <= i < \length(ll) ==> \separated(\nth(ll, i), item) ;
  */
  
  ((struct list *)item)->next = NULL;
  //@ ghost BIN: ;

  //@ assert Unchanged1: unchanged{AR, BIN}(to_logic_list{AR}(\at(*list, AR), NULL)) ;
  //@ assert LinkedItem: linked_ll(item, NULL, to_logic_list(item, NULL));

  /*@ assigns \nothing ;
      ensures ItemStillNotIn: !in_list(item, to_logic_list(*list, NULL)) ;
  */ {
    //@ assert ISNI_1: ptr_separated_from_list(item, to_logic_list(*list, NULL));
    /*@ assert ISNI_2: \let ll = to_logic_list(*list, NULL) ;
        \forall integer i ; 0 <= i < \length(ll) ==> \nth(ll, i) != item ;
    */
  }    

  l = list_tail(list);
  //@ assert L_in_Old: l == NULL || in_list(l, to_logic_list{Pre}(\at(*list, Pre), NULL)) ;
  
  //@ assert HandlerSep:    dptr_separated_from_list(list, to_logic_list(*list, NULL));
  
  if(l == NULL) {
    *list = item;
    //@ assert HandlerSep_NULL:    dptr_separated_from_list(list, to_logic_list(*list, NULL));
  } else {
    //@ assert \at(*list, Pre) != NULL ;

    //@ ghost BN: ;

    /*@ assigns \nothing ;
        ensures RememberList: to_logic_list{BN}(*list, NULL) == to_logic_list{AR}(*list, NULL) ;
    */ {
      //@ assert RL_1: linked_ll{AR}(*list, NULL, to_logic_list{AR}(*list, NULL));
      //@ assert RL_2: unchanged{AR, BN}(to_logic_list{AR}(*list, NULL)) ;
    }
    
    /*@ assigns \nothing ;
        ensures ND: linked_ll{BN}(*list, l, to_logic_list{BN}(*list, l)) ;
	ensures LC: to_logic_list{BN}(*list, NULL) == (to_logic_list{BN}(*list, l) ^ [| l |]);
    */ {
      //@ assert ND1: *list == l ==> linked_ll{BN}(*list, l, to_logic_list{BN}(*list, l)) ;

      /*@ assert ND2: *list != l ==>
	  \let ll = to_logic_list{BN}(*list, NULL) ; \nth(ll, \length(ll)-1) == l ;
      */
      /*@ assert ND2: *list != l ==>
	  \let ll = to_logic_list{BN}(*list, NULL) ; \nth(ll, \length(ll)-1)->next == NULL ;
      */
      //@ assert ND2: \valid(l) && l->next == NULL ==> to_logic_list(l, NULL) == [| l |] ;
      //@ assert ND2: \length(to_logic_list{BN}(l, NULL)) == 1 ; 
      /*@ assert ND2: *list != l ==> \let ll = to_logic_list{BN}(*list, NULL) ; 
	  \nth(ll, \length(ll)-\length(to_logic_list{BN}(l, NULL))) == l ;
      */
      /*@ assert ND2: *list != l ==> to_logic_list{BN}(*list, NULL) ==
	  (to_logic_list{BN}(*list, l) ^ to_logic_list{BN}(l, NULL));
      */
      /*@ assert ND2: linked_ll{BN}(*list, NULL, to_logic_list{BN}(*list, l) ^ 
	                                      to_logic_list{BN}(l, NULL));
      */
      //@ assert ND2: *list != l ==> to_logic_list{BN}(*list, l) != \Nil ;
      //@ assert ND2: to_logic_list{BN}(l, NULL) != \Nil ;
      /*@ assert ND2: linked_ll{BN}(*list, l, to_logic_list{BN}(*list, l)) && 
	              linked_ll{BN}(l, NULL, to_logic_list{BN}(l, NULL)) ;
      */
    } 

    l->next = item;
    //@ ghost AN: ;

    /*@ assigns \nothing ;
        ensures LinkedPost: linked_ll{AN}(*list, item->next, to_logic_list{AN}(*list, item->next)) ;
	ensures HSepPost: dptr_separated_from_list(list, to_logic_list{AN}(*list, item->next));
	ensures NewList_1: to_logic_list{AN}(*list, NULL) == 
	                 (to_logic_list{BN}(*list, NULL) ^ [| item |]) ;
    */ {
      /*@ assert SeparationEnd: \let ll = to_logic_list{BN}(\at(*list, BN), l) ;
	  \forall integer i ; 0 <= i < \length(ll) ==> \separated(\nth(ll, i), l) ;
      */
      //@ assert Post12: \at(*list, BN) == \at(*list, AN) ;
      /*@ assert Post111:
	  \forall struct list* e ; \separated(e, l) ==> \at(e->next, BN) == \at(e->next, AN);
      */
      //@ assert Post11: unchanged{BN, AN}(to_logic_list{BN}(\at(*list, BN), l));
      //@ assert Post1: linked_ll{AN}(*list, l, to_logic_list{AN}(*list, l)) ;

      //@ assert Post21: \separated(l, item) ;
      //@ assert Post22: linked_ll{AN}(item, item->next, to_logic_list{AN}(item, item->next)) ;
      //@ assert Post2: linked_ll{AN}(l, item->next, to_logic_list{AN}(l, item->next)) ;

      /*@ assert Post3: all_separated_in_list(to_logic_list{AN}(*list, l) ^ 
	                                      to_logic_list{AN}(l, item->next));
      */
      //@ assert HSP1: dptr_separated_from_list(list, to_logic_list{AN}(*list, l));
      //@ assert HSP2: dptr_separated_from_list(list, to_logic_list{AN}(item, item->next));

      /*@ assert NL_1: to_logic_list{BN}(*list, NULL) == 
	         (to_logic_list{BN}(*list, l) ^ [| l |]) ;
      */
      /*@ assert NL_2: to_logic_list{AN}(*list, NULL) ==
	         (to_logic_list{BN}(*list, l) ^ to_logic_list{AN}(l, NULL));
      */
    }

    /*@
      assigns \nothing ;
      ensures to_logic_list{AN}(\at(*list, AN), NULL) == 
             (to_logic_list{BN}(\at(*list, BN), NULL) ^ [| item |]) ;
      ensures does_not_contain_begin:
        \at(*list, Pre) != NULL ==>
        !in_list(item, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
          to_logic_list{BN}(\at(*list, BN), NULL) == to_logic_list{Pre}(\at(*list, Pre), NULL) ;
      ensures contains_value:
        \let old_list = \at(*list, Pre) ; old_list != NULL ==>
        in_list(item, to_logic_list{Pre}(old_list, NULL)) ==>
          to_logic_list{BN}(\at(*list, BN), NULL) ==
         (to_logic_list{Pre}(old_list, item) ^ to_logic_list{Pre}(\at(item->next, Pre), NULL)) ;
      ensures contains_length:
        \let old_list = \at(*list, Pre) ; old_list != NULL ==>
        in_list(item, to_logic_list{Pre}(old_list, NULL)) ==>
	  \length(to_logic_list{BN}(\at(*list, BN), NULL)) ==
	  \length(to_logic_list{Pre}(old_list, NULL)) - 1 ;
    */ {}
  }
}
/*---------------------------------------------------------------------------*/
/**
 * Add an item to the start of the list.
 */
void
list_push(list_t list, void *item)
{
  /* Make sure not to add the same element twice */
  list_remove(list, item);

  //@ ghost AR: ;
  
  /*@ assert SepReformulation: \let ll = to_logic_list(*list, NULL) ;
      \forall integer i ; 0 <= i < \length(ll) ==> \separated(\nth(ll, i), item) ;
  */

  ((struct list *)item)->next = *list;

  //@ assert unchanged{AR, Here}(to_logic_list{AR}(\at(*list, AR), NULL));
  //@ assert to_logic_list(item, NULL) == ([| item |] ^ to_logic_list(*list, NULL));
  //@ ghost Inter: ;

  //@ assert \separated(list, item);
  //@ assert dptr_separated_from_list(list, to_logic_list(item, NULL));
  /*@ assert SepReformulation: \let ll = to_logic_list(*list, NULL) ;
      \forall integer i ; 0 <= i < \length(ll) ==> \separated(\nth(ll, i), list) ;
  */

  
  *list = item;
  
  //@ assert unchanged{Inter, Here}(to_logic_list{Inter}(\at(item, Inter), NULL));
  //@ assert to_logic_list(*list, NULL) == ([| item |] ^ to_logic_list{AR}(\at(*list, AR), NULL));
}
/*---------------------------------------------------------------------------*/
/**
 * Remove the last object on the list.
 *
 * This function removes the last object on the list and returns it.
 *
 * \param list The list
 * \return The removed object
 *
 */
void *
list_chop(list_t list)
{
  struct list *l, *r;

  if(*list == NULL) {
    return NULL;
  }
  if(((struct list *)*list)->next == NULL) {
    l = *list;
    *list = NULL;
    return l;
  }

  /*@ loop invariant \nth(to_logic_list(*list, NULL), n) == l && l != NULL;
    @ loop invariant \nth(to_logic_list(*list, NULL), n+1) == l->next && l->next != NULL;
    @ loop invariant linked_ll(*list, NULL, to_logic_list(*list, NULL));
    @ loop invariant linked_ll(*list, l, to_logic_list(*list, l));
    @ loop invariant linked_ll(l, NULL, to_logic_list(l, NULL));
    @ loop invariant n == \length(to_logic_list(*list, l));
    @ loop invariant 0 <= n <= \length(to_logic_list(*list, NULL)) - 2;
    @ loop invariant unchanged{Pre, Here}(to_logic_list(*list, NULL)) ;
    @ loop invariant dptr_separated_from_list(list, to_logic_list(*list, NULL));
    @ loop assigns l, n ;
    @ loop variant \length(to_logic_list(l->next, NULL)); 
    @*/
  for(l = *list; l->next->next != NULL; l = l->next);

  //@ assert in_list(l, to_logic_list(*list, NULL)) ;
  /*@ assert 
      linked_ll(*list, NULL, to_logic_list(*list, NULL)) ==>
        linked_ll(*list, l, to_logic_list(*list, l)) &&
	linked_ll(l, NULL, to_logic_list(l, NULL)) ;
  */
  //@ ghost PreM: ;
  //@ assert ptr_separated_from_list(l, to_logic_list(*list, l)) ;
  //@ assert to_logic_list(*list, l->next) == (to_logic_list(*list, l) ^ [| l |]) ;
  r = l->next;
  l->next = NULL;
  //@ assert unchanged{PreM,Here}(to_logic_list{PreM}(*list, l)) ;
  //@ assert to_logic_list(*list, l->next) == (to_logic_list(*list, l) ^ [| l |]) ;
  
  //@ assert linked_ll(*list, l, to_logic_list(*list, l)) ;
  //@ assert linked_ll(*list, l->next, to_logic_list(*list, l->next)) ;
  
  return r;
}
/*---------------------------------------------------------------------------*/
/**
 * Remove the first object on a list.
 *
 * This function removes the first object on the list and returns a
 * pointer to it.
 *
 * \param list The list.
 * \return Pointer to the removed element of list.
 */
/*---------------------------------------------------------------------------*/
void *
list_pop(list_t list)
{
  struct list *l;
  l = *list;
  if(*list != NULL) {
    //@ ghost struct list* next = (*list)->next ;
    *list = ((struct list *)*list)->next;
    //@ assert unchanged{Pre, Here}(to_logic_list{Pre}(next, NULL));
  }

  return l;
}
/*---------------------------------------------------------------------------*/
/**
 * Remove a specific element from a list.
 *
 * This function removes a specified element from the list.
 *
 * \param list The list.
 * \param item The item that is to be removed from the list.
 *
 */
/*---------------------------------------------------------------------------*/
void
list_remove(list_t list, void *item)
{
  /*@ assert ! in_list(item, to_logic_list(*list, NULL)) ==>
             (\forall integer n ; 0 <= n < \length(to_logic_list(*list, NULL)) ==> 
                \nth(to_logic_list(*list, NULL), n) != item) ;
  */
  if( *list == NULL ){
    /*@ assert 
        \forall struct list* e ; (in_list(e, to_logic_list(*list, NULL)) && e->next == item) ==>
	  \false ;
    */
    return ;
  }
  if( *list == item ){
    //@ assert to_logic_list(*list, item) == \Nil ;
    /*@ assert 
        \forall struct list* e ; (in_list(e, to_logic_list(*list, NULL)) && e->next == item) ==>
	  \false ;
    */
    //@ ghost struct list* next = (*list)->next ;

    /*@
      assigns \nothing ;
      ensures Where_is_l: \forall struct list* l ; l != item ==> (
        in_list(l, to_logic_list(item, NULL)) <==> in_list(l, to_logic_list(item->next, NULL))) ;
    */ {
      /*@ assert R1:
	  ptr_separated_from_list(item, to_logic_list(item->next, NULL)) ==>
            !in_list(item, to_logic_list(item->next, NULL)) ;
      */
      /*@ assert R21: to_logic_list(item, NULL) ==
	              (to_logic_list(item, item->next) ^ to_logic_list(item->next, NULL)) ;
      */
      /*@ assert R22:
	\forall struct list* l ; 
	(in_list(l, to_logic_list(item, NULL)) <==> (
	 in_list(l, to_logic_list(item, item->next)) ||
	 in_list(l, to_logic_list(item->next, NULL)))) ;
      */
      //@ assert R23: to_logic_list(item, item->next) == [| item |] ;
      //@ assert R24: \forall struct list* l ; l != item ==> !in_list(l, [| item |]) ;
    }
      

    *list = (*list)->next ;
    //@ assert UnchangedTailChangedHead: unchanged{Pre, Here}(to_logic_list{Pre}(next, NULL));
    //@ assert PostLinkedChangedHead: linked_ll(*list, NULL, to_logic_list(*list, NULL)) ;
    /*@ assert Remains:
        \forall struct list* l ; l != item ==>
          (in_list(l, to_logic_list{Pre}(\at(*list, Pre), NULL)) <==>
           in_list(l, to_logic_list{Here}(\at(*list, Here), NULL))) ;
    */
    /*@ assert NewList:
        (to_logic_list{Pre}(\at(*list,Pre), item) ^ to_logic_list{Pre}(item->next, NULL)) ==
	 to_logic_list(*list, NULL) ;
    */

    return ;
  }

  struct list *l = *list ;
  int n = 0 ;
  /*@ loop invariant \nth(to_logic_list(*list, NULL), n) == l && l != NULL;
    @ loop invariant linked_ll(*list, NULL, to_logic_list(*list, NULL));
    @ loop invariant linked_ll(*list, l, to_logic_list(*list, l));
    @ loop invariant linked_ll(l, NULL, to_logic_list(l, NULL));
    @ loop invariant n == \length(to_logic_list(*list, l));
    @ loop invariant 0 <= n <= \length(to_logic_list(*list, NULL)) - 1;
    @ loop invariant unchanged{Pre, Here}(to_logic_list(*list, NULL)) ;
    @ loop invariant \forall integer j ; 0 <= j <= n ==> 
    @                  \nth(to_logic_list(*list, NULL), j) != item ;
    @ loop invariant ptr_separated_from_list(item, to_logic_list(*list, l)) ;
    @ loop invariant dptr_separated_from_list(list, to_logic_list(*list, NULL)) ;
    @ loop assigns l, n ;
    @ loop variant \length(to_logic_list(l->next, NULL)); 
    @*/
  while(l->next != item && l->next != NULL){
    //@ assert in_list(l->next, to_logic_list(*list, NULL)) ;
    //@ assert all_separated_in_list(to_logic_list(*list, NULL)) ;
    //@ assert in_list(l, to_logic_list(*list, NULL)) ;
    //@ assert to_logic_list(*list, NULL) == (to_logic_list(*list, l) ^ to_logic_list(l, NULL)) ;
    /*@ assert \forall integer i ; 0 <= i < \length(to_logic_list(*list, l)) ==>
        \separated(\nth(to_logic_list(*list, NULL), i),
	           \nth(to_logic_list(*list, NULL), \length(to_logic_list(*list, l))+1)) ;
    */
    //@ assert \nth(to_logic_list(*list, NULL), \length(to_logic_list(*list, l))+1) == l->next ;
    /*@ assert \forall integer i ; 0 <= i < \length(to_logic_list(*list, l)) ==>
        \nth(to_logic_list(*list, NULL), i) == \nth(to_logic_list(*list, l), i) ;
    */
    //@ assert ptr_separated_from_list(l->next, to_logic_list(*list, l)) ;
    //@ assert to_logic_list(*list, l->next) == (to_logic_list(*list, l) ^ [| l |]) ;
    l = l->next ;
    ++n;
  }
  /*@ assert \forall integer j ; 0 <= j <= n ==> 
               \nth(to_logic_list(*list, NULL), j) != item ;
  */
  if( l->next == item ){
    /*@ assert
        \forall struct list* e ; (in_list(e, to_logic_list(*list, NULL)) && e->next == item) ==>
	  e == l ;
    */

    //@ assert n+1 < \length(to_logic_list(*list, NULL)) ;
    //@ assert \nth(to_logic_list(*list, NULL), n+1) == item ;

    /*@ assigns \nothing ;
        ensures OldLeft: linked_ll(*list, l->next, to_logic_list(*list, l->next));
	ensures ItemNotInOldLeft: ptr_separated_from_list(item, to_logic_list(*list, l->next));
    */{
      //@ assert OL_In: in_list(l->next, to_logic_list(*list, NULL));
    }

    //@ assert OldRight: linked_ll(l->next->next, NULL, to_logic_list(l->next->next, NULL));

    //@ ghost BR: ;
    l->next = l->next->next ;
    //@ ghost AR: ;
    
    /*@ assigns \nothing ;
        ensures NewLeft:  \let hlist = \at(*list, AR) ; \let ln = \at(l->next, AR) ;
	  linked_ll{AR}(hlist, ln, to_logic_list(hlist, ln));
	ensures NewLeftVal: 
	  to_logic_list{AR}(\at(*list,AR), \at(l->next, AR)) == 
	  to_logic_list{BR}(\at(*list,BR), item) ;
	ensures ItemNotInNewLeft: 
	  ptr_separated_from_list(item, to_logic_list{AR}(\at(*list, AR), \at(l->next, AR))) ;
	ensures HandlerSepNewLeft: 
	  dptr_separated_from_list(list, to_logic_list{AR}(\at(*list, AR), \at(l->next, AR))) ;
    */ {
      /*@ assert SplitLeftP1: in_list(l, to_logic_list{BR}(\at(*list, BR), NULL)) ==>
	  to_logic_list{BR}(\at(*list, BR), NULL) ==
	  (to_logic_list{BR}(\at(*list, BR), l) ^ to_logic_list{BR}(l, NULL));
      */
      /*@ assert SplitLeftP2:
	  to_logic_list{BR}(l, NULL) ==
	  (to_logic_list{BR}(l, \at(l->next, BR)) ^ to_logic_list{BR}(\at(l->next, BR), NULL));
      */
      /*@ assert SplitLeft:
	  to_logic_list{BR}(\at(*list, BR), NULL) == 
	  (to_logic_list{BR}(\at(*list, BR), l) ^ [| l |] ^ to_logic_list{BR}(item, NULL));
      */
      /*@ assert C3: 
	  \let left = to_logic_list{BR}(\at(*list, BR), l); 
	  \let all  = to_logic_list{BR}(\at(*list, BR), NULL) ;
	  l->next == \nth(all, \length(left) + 2) || l->next == NULL ;
      */
      /*@ assert C4:
	  \let left = to_logic_list{BR}(\at(*list, BR), l); 
	  \let all  = to_logic_list{BR}(\at(*list, BR), NULL) ;
	  \forall integer i ; 0 <= i < \length(left) ==> \nth(left, i) == \nth(all, i) ;
      */

      /*@ assigns \nothing ; 
	ensures SepEndLeftPre:
	ptr_separated_from_list(l->next, to_logic_list{BR}(\at(*list, BR), l)) ;
      */ {
	//@ assert all_separated_in_list(to_logic_list{BR}(\at(*list, BR), NULL)) ;
	/*@ assert SepEndLeftPre_P1:
	  \let left = to_logic_list{BR}(\at(*list, BR), l); 
	  \let all  = to_logic_list{BR}(\at(*list, BR), NULL) ;
	  \forall integer i, j ; 0 <= i < \length(left) && \length(left) <= j < \length(all) ==> 
	    \separated(\nth(all, i), \nth(all, j)) &&
	    \separated(\nth(all, i), (struct list*) NULL);
	*/
	/*@ assert SepEndLeftPre_P2_P:
	  \let left = to_logic_list{BR}(\at(*list, BR), l); 
	  \let all  = to_logic_list{BR}(\at(*list, BR), NULL) ;
	  \length(left) <= \length(left) + 2 < \length(all) || l->next == NULL ;
	*/
	/*@ assert SepEndLeftPre_P2_1:
	  \let left = to_logic_list{BR}(\at(*list, BR), l); 
	  \let all  = to_logic_list{BR}(\at(*list, BR), NULL) ;
	  \forall integer i ; 0 <= i < \length(left) && \length(left) + 2 < \length(all) ==> 
	    \separated(\nth(left, i), \nth(all, \length(left) + 2)) ;
	*/
	/*@ assert SepEndLeftPre_P2_2:
	  \let left = to_logic_list{BR}(\at(*list, BR), l); 
	  \let all  = to_logic_list{BR}(\at(*list, BR), NULL) ;
	  \forall integer i ; 0 <= i < \length(left) ==> 
	    \separated(\nth(left, i), (struct list*) NULL) ;
	*/
      }
      /*@ assert SepItemLeftPre: 
	  ptr_separated_from_list(item, to_logic_list{BR}(\at(*list, BR), l)) ;
      */
      //@ assert SepItemL: \separated(l, item);
      
      //@ assert NL_NI: ptr_separated_from_list(l, to_logic_list{BR}(\at(*list, BR), \at(l, AR))) ;
      //@ assert UnchangedLeft: unchanged{BR, AR}(to_logic_list{BR}(\at(*list, BR), \at(l, AR))) ;
      /*@ assert EqLeftP1: to_logic_list{BR}(\at(*list, BR), \at(l, AR)) == 
	                   to_logic_list{AR}(\at(*list, AR), \at(l, AR)) ;
      */
      /*@ assert OldLeftVal: 
	  to_logic_list{BR}(\at(*list, BR), item) == 
	  (to_logic_list{BR}(\at(*list, BR), \at(l, AR)) ^ [| l |]) ;
      */
      /* @ assert NewLeftVal: 
	  to_logic_list{AR}(\at(*list, AR), \at(l->next, AR)) == 
	  (to_logic_list{AR}(\at(*list, AR), l) ^ [| l |]) ;
      */
      //@ assert NewLeftP1 : linked_ll{AR}(\at(*list, AR), l, to_logic_list{AR}(\at(*list, AR), l));
      /*@ assert SepHandlerPre:
	  dptr_separated_from_list(list, to_logic_list{BR}(\at(*list, BR), NULL)) <==>
	  (dptr_separated_from_list(list, to_logic_list{BR}(\at(*list, BR), l)) &&
           dptr_separated_from_list(list, to_logic_list{BR}(l, NULL))) ;
      */
      /*@ assert SepHandlerLeftPreP1: 
	  dptr_separated_from_list(list, to_logic_list{BR}(\at(*list, BR), l)) ;
      */
      /*@ assert SepHandlerLeftPreP2: 
	  dptr_separated_from_list(list, to_logic_list{AR}(\at(*list, AR), l)) ;
      */
      /*@ assert PostNewLeftValue: 
	  to_logic_list{AR}(\at(*list, AR), \at(l->next, AR)) == 
	  to_logic_list{BR}(\at(*list, BR), item) ;
      */
      //@ assert SepHandlerEnd: \separated(l, list);
    }

    /*@ assigns \nothing ;
        ensures NewRight: linked_ll(l->next, NULL, to_logic_list(l->next, NULL));
	ensures ItemNotInNewRight: ptr_separated_from_list(item, to_logic_list(l->next, NULL)) ;
	ensures HandlerSepNewRight: dptr_separated_from_list(list, to_logic_list(l->next, NULL)) ;
	ensures NewRightVal: to_logic_list(l->next, NULL) == to_logic_list{BR}(item->next, NULL) ;
    */ {
      //@ assert NR_NI: ! in_list(l, to_logic_list{Pre}(\at(l->next, Here), NULL)) ;
      /*@ assert 
	  SepItemRightPre: ptr_separated_from_list(item, to_logic_list{BR}(item->next, NULL)) ;
      */
      /*@ assert SplitRight:
	  to_logic_list{BR}(*list, NULL) == 
	  (to_logic_list{BR}(*list, item) ^ to_logic_list{BR}(item, NULL));
      */
      /*@ assert SepHandlerRightPreP1: 
	  dptr_separated_from_list(list, to_logic_list{BR}(item, NULL)) ;
      */
      /*@ assert SepHandlerRightPreP2: 
	  dptr_separated_from_list(list, to_logic_list{BR}(item->next, NULL)) ;
      */
      //@ assert UnchangedRight: unchanged{BR, Here}(to_logic_list{Pre}(\at(l->next, Here), NULL)) ;
    }

    /*@ assigns \nothing ;
        ensures AllSepNew:
	  \let left  = to_logic_list{BR}(*list, item) ;
	  \let right = to_logic_list{BR}(item->next, NULL) ;
	  all_separated_in_list(left ^ right);
     */ {
      /*@ assert Split:
	  to_logic_list{BR}(*list, NULL) == 
	  (to_logic_list{BR}(*list, item) ^ [|item|] ^ to_logic_list{BR}(item->next, NULL));
      */
      //@ assert AllSepOld: all_separated_in_list(to_logic_list{BR}(*list, NULL));
    }

    //@ assert PostLinkedRemove: linked_ll(*list, NULL, to_logic_list(*list, NULL)) ;

    //@ assert SeparatedItemLeft: ptr_separated_from_list(item, to_logic_list(*list, l->next));
    //@ assert SeparatedItemRight: ptr_separated_from_list(item, to_logic_list(l->next, NULL));
    //@ assert PostNotInRemove: ptr_separated_from_list(item, to_logic_list(*list, NULL)) ;

    /*@ assigns \nothing ;
        ensures PostNewList:
	        (to_logic_list{Pre}(\old(*list), item) ^ to_logic_list{Pre}(item->next, NULL)) ==
	        to_logic_list(*list, NULL) ;
    */ {
      //@ assert PostNL_P1: to_logic_list{Pre}(*list, item) == to_logic_list(*list, l->next) ;
      //@ assert PostNL_P2: to_logic_list{Pre}(item->next, NULL) == to_logic_list(l->next, NULL) ;
      /*@ assert PostNL_P3: to_logic_list(*list, NULL) ==
	  (to_logic_list(*list, l->next) ^ to_logic_list(l->next, NULL));
      */
    }

    /*@
      assigns \nothing ;
      ensures Remains:
        \forall struct list* l ; l != item ==>
          (in_list(l, to_logic_list{Pre}(\at(*list, Pre), NULL)) <==>
           in_list(l, to_logic_list{Here}(\at(*list, Here), NULL))) ;
    */ {
      /*@ assert PIn_Split_New: in_list(item, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
           to_logic_list{Here}(\at(*list, Here), NULL) ==
	    (to_logic_list{Pre}(\at(*list, Pre), item) ^ 
	     to_logic_list{Pre}(\at(item->next, Pre), NULL));
      */
      /*@ assert PIn_Split_Old_P2: in_list(item, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
           to_logic_list{Pre}(item, NULL) ==
            (to_logic_list{Pre}(item, \at(item->next, Pre)) ^ 
             to_logic_list{Pre}(\at(item->next, Pre), NULL));
      */
      /*@ assert PInP: in_list(item, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
          \forall struct list* l ; in_list(l, to_logic_list{Pre}(\at(*list, Pre), NULL)) <==>
	  (   in_list(l, to_logic_list{Pre}(\at(*list, Pre), item))
	   || in_list(l, [| item |] )
	   || in_list(l, to_logic_list{Pre}(\at(item->next, Pre), NULL))) ;
      */
      /*@ assert PNotInItem: \forall struct list* l ; l != item <==> !in_list(l, [| item |] ) ; */
      /*@ assert PInP2: in_list(item, to_logic_list{Pre}(\at(*list,Pre), NULL)) ==>
	\forall struct list* l ; l != item ==> (
	 in_list(l, to_logic_list{Pre}(\at(*list, Pre), NULL)) <==>
	 (  in_list(l, to_logic_list{Pre}(\at(*list, Pre), item))
	 || in_list(l, to_logic_list{Pre}(\at(item->next, Pre), NULL)))) ;
      */
      /*@ assert PIn: in_list(item, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	\forall struct list* l ; l != item ==> (
	  in_list(l, to_logic_list{Pre}(\at(*list, Pre), NULL)) <==>
	  in_list(l, to_logic_list{Here}(\at(*list, Here), NULL))) ;
      */
    }
  } else {
    //@ assert l->next == NULL ;
    /*@ assert \forall integer j ; 0 <= j <= n ==> 
                  \nth(to_logic_list(*list, NULL), j) != item ;
    */
    /*@ assert 
        \forall struct list* e ; (in_list(e, to_logic_list(*list, NULL)) && e->next == item) ==>
	  \false ;
    */
    
    //@ assert UnchangedNoChange: unchanged{Pre, Here}(to_logic_list{Pre}(*list, NULL)) ;
    //@ assert PostLinkedNoChange: linked_ll(*list, NULL, to_logic_list(*list, NULL)) ;
  }
}
/*---------------------------------------------------------------------------*/
/**
 * Get the length of a list.
 *
 * This function counts the number of elements on a specified list.
 *
 * \param list The list.
 * \return The length of the list.
 */
/*---------------------------------------------------------------------------*/
int
list_length(list_t list)
{
  struct list *l;
  int n = 0;

  /*@ loop invariant linked_ll(l, NULL, to_logic_list(l, NULL));
    @ loop invariant linked_ll(*list, NULL, to_logic_list(*list, NULL));
    @ loop invariant n == \length(to_logic_list(*list, NULL)) - 
    @                     \length(to_logic_list(l, NULL));
    @ loop assigns l, n ;
    @ loop variant \length(to_logic_list(l, NULL)); 
    @*/
  for(l = *list; l != NULL; l = l->next) {
    ++n;
  }

  return n;
}
/*---------------------------------------------------------------------------*/
/**
 * \brief      Insert an item after a specified item on the list
 * \param list The list
 * \param previtem The item after which the new item should be inserted
 * \param newitem  The new item that is to be inserted
 * \author     Adam Dunkels
 *
 *             This function inserts an item right after a specified
 *             item on the list. This function is useful when using
 *             the list module to ordered lists.
 *
 *             If previtem is NULL, the new item is placed at the
 *             start of the list.
 *
 */
void
list_insert(list_t list, void *previtem, void *newitem)
{
  if(previtem == NULL) {
    list_push(list, newitem);
  } else {
    //@ ghost list_split(list, newitem, NULL) ;

    /*@ assigns \nothing ;
      ensures in_list(newitem, to_logic_list{Pre}(*list, NULL)) ==>
        in_list(previtem, to_logic_list{Pre}(newitem, NULL)) ==>
	in_list(previtem->next, to_logic_list{Pre}(newitem->next, NULL)) || previtem->next == NULL ;
      ensures in_list(newitem, to_logic_list{Pre}(*list, NULL)) ==>
        in_list(previtem, to_logic_list{Pre}(newitem, NULL)) ==>
	in_list(previtem, to_logic_list{Pre}(newitem->next, NULL)) ;
      ensures in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
        in_list(previtem, to_logic_list{Pre}(newitem, NULL)) ==> 
	previtem->next != newitem ;
      ensures in_list(newitem, to_logic_list{Pre}(*list, NULL)) ==>
        in_list(previtem, to_logic_list{Pre}(newitem, NULL)) ==>
        linked_ll{Pre}(newitem->next, NULL, to_logic_list{Pre}(newitem->next, NULL)) ;
    */ {
      /*@ assert in_list(newitem, to_logic_list{Pre}(*list, NULL)) ==>
	  in_list(previtem, to_logic_list{Pre}(newitem, NULL)) ==>
	  linked_ll{Pre}(newitem->next, NULL, to_logic_list{Pre}(newitem->next, NULL)) &&
	  ptr_separated_from_list(newitem, to_logic_list{Pre}(newitem->next, NULL)) ;
      */
      /*@ assert in_list(newitem, to_logic_list{Pre}(*list, NULL)) ==>
	in_list(previtem, to_logic_list{Pre}(newitem, NULL)) ==>
	to_logic_list{Pre}(newitem, NULL) == 
	([| newitem |] ^ to_logic_list{Pre}(newitem->next, NULL)) ;
      */
      /*@ assert in_list(newitem, to_logic_list{Pre}(*list, NULL)) ==>
	in_list(previtem, to_logic_list{Pre}(newitem, NULL)) ==>
	!in_list(previtem, [| newitem |]) ;
      */
      /*@ assert in_list(newitem, to_logic_list{Pre}(*list, NULL)) ==>
	in_list(previtem, to_logic_list{Pre}(newitem, NULL)) ==>
	in_list(previtem, to_logic_list{Pre}(newitem->next, NULL)) ;
      */
      /*@ assert in_list(newitem, to_logic_list{Pre}(*list, NULL)) ==>
	in_list(previtem, to_logic_list{Pre}(newitem->next, NULL)) ==>
	in_list(previtem->next, to_logic_list{Pre}(newitem->next, NULL)) || previtem->next == NULL ;
      */
    }
    
    if(previtem->next != newitem){
      //@ ghost list_split(list, previtem->next, NULL) ;

      /*@ assigns \nothing ;
	ensures in_list(newitem, to_logic_list{Pre}(*list, NULL)) ==>
	in_list(previtem, to_logic_list{Pre}(*list, newitem)) ==>
	to_logic_list{Pre}(*list, newitem) ==
	(to_logic_list{Pre}(*list, previtem->next) ^ to_logic_list{Pre}(previtem->next, newitem)) ;
      */ {
	/*@ assert in_list(newitem, to_logic_list{Pre}(*list, NULL)) ==>
	  in_list(previtem, to_logic_list{Pre}(*list, newitem)) ==>
	  in_list(previtem->next, to_logic_list{Pre}(*list, newitem)) ;
	*/
      }

      /*@ assigns \nothing ;
	ensures in_list(newitem, to_logic_list{Pre}(*list, NULL)) ==>
	in_list(previtem, to_logic_list{Pre}(newitem, NULL)) ==>
	to_logic_list{Pre}(newitem->next, NULL) ==
	(to_logic_list{Pre}(newitem->next, previtem->next) ^ to_logic_list{Pre}(previtem->next, NULL)) ;
      */ {
	/*@ assert in_list(newitem, to_logic_list{Pre}(*list, NULL)) ==>
	  in_list(previtem, to_logic_list{Pre}(newitem, NULL)) ==>
	  linked_ll{Pre}(newitem->next, NULL, to_logic_list{Pre}(newitem->next, NULL)) ;
	*/
	/*@ assert in_list(newitem, to_logic_list{Pre}(*list, NULL)) ==>
	  in_list(previtem, to_logic_list{Pre}(newitem, NULL)) ==>
	  to_logic_list{Pre}(newitem, NULL) == 
	           ([| newitem |] ^ to_logic_list{Pre}(newitem->next, NULL)) ;
	*/
	/*@ assert in_list(newitem, to_logic_list{Pre}(*list, NULL)) ==>
	  in_list(previtem, to_logic_list{Pre}(newitem, NULL)) ==>
	  !in_list(previtem, [| newitem |]) ;
	*/
	/*@ assert in_list(newitem, to_logic_list{Pre}(*list, NULL)) ==>
	  in_list(previtem, to_logic_list{Pre}(newitem, NULL)) ==>
	  in_list(previtem, to_logic_list{Pre}(newitem->next, NULL)) ;
	*/
      }
      
      list_remove(list, newitem);

      //@ ghost AR: ; 
      
      //@ assert \at(previtem->next, AR) == \at(previtem->next, Pre) ;
      //@ assert \at(newitem->next, AR) == \at(newitem->next, Pre) ;

      /*@ assigns \nothing ;
	ensures in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	in_list(previtem, to_logic_list{Pre}(\at(*list, Pre), newitem)) ==>
	to_logic_list{AR}(\at(*list, AR), \at(previtem->next, AR)) == 
	to_logic_list{Pre}(\at(*list, Pre), \at(previtem->next, Pre)) ;
      */ {
	/*@ assert in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	  in_list(previtem, to_logic_list{Pre}(\at(*list, Pre), newitem)) ==>
	  (to_logic_list{AR}(\at(*list, AR), \at(previtem->next, AR)) ^
	   to_logic_list{AR}(\at(previtem->next, AR), NULL))
	   ==
	  (to_logic_list{Pre}(\at(*list, Pre), \at(previtem->next, AR)) ^ 
	   to_logic_list{Pre}(\at(previtem->next, AR), newitem) ^
	   to_logic_list{Pre}(\at(newitem->next, Pre), NULL)) ;
	*/
	/*@ assigns \nothing ;
	    ensures in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	    in_list(\at(previtem->next, Pre), to_logic_list{Pre}(\at(*list, Pre), newitem)) ==>
	      unchanged{Pre, AR}(to_logic_list{Pre}(\at(*list, Pre), \at(previtem->next, Pre))) ;
	*/ {
	  /*@ assert in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	    \let ll = to_logic_list{Pre}(\at(*list, Pre), newitem) ;
	    \forall integer i ; 0 <= i < \length(ll)-1 ==> 
	    (\valid{Pre}(\at(\nth(ll, i), Pre)) && \valid{AR}(\at(\nth(ll, i), AR)) &&
	     \at(\nth(ll, i)->next, Pre) == \at(\nth(ll, i)->next, AR)) ;
	  */
	  /*@ assert in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	    \let ll = to_logic_list{Pre}(\at(*list, Pre), newitem) ;
	    in_list(\at(previtem->next, Pre), ll) ==>
	    to_logic_list{Pre}(\at(*list, Pre), newitem) ==
	    (to_logic_list{Pre}(\at(*list, Pre), \at(previtem->next, Pre)) ^ 
	     to_logic_list{Pre}(\at(previtem->next, Pre), newitem)) &&
	    linked_ll{Pre}(\at(*list, Pre), \at(previtem->next, Pre), 
	                to_logic_list{Pre}(\at(*list, Pre), \at(previtem->next, Pre))) &&
            linked_ll{Pre}(\at(previtem->next, Pre), newitem, 
	                to_logic_list{Pre}(\at(previtem->next, Pre), newitem)) ;
	  */
	  /*@ assert in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	    \let ll = to_logic_list{Pre}(\at(*list, Pre), newitem) ;
	    in_list(\at(previtem->next, Pre), ll) ==>
	    \let sll = to_logic_list{Pre}(\at(*list, Pre), \at(previtem->next, Pre)) ;
	    \forall integer i ; 0 <= i < \length(sll) ==>
	    (\valid{Pre}(\at(\nth(ll, i), Pre)) && \valid{Pre}(\at(\nth(sll, i), Pre)) &&
	      \at(\nth(sll, i)->next, Pre) == \at(\nth(ll, i)->next, Pre)) ;
	  */
	  /*@ assert in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	    \let ll = to_logic_list{Pre}(\at(*list, Pre), newitem) ;
	    in_list(\at(previtem->next, Pre), ll) ==>
	    \let sll = to_logic_list{Pre}(\at(*list, Pre), \at(previtem->next, Pre)) ;
	      \length(sll) <= \length(ll)-1 ;
	  */
	  /*@ assert in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	    \let ll = to_logic_list{Pre}(\at(*list, Pre), newitem) ;
	    in_list(\at(previtem->next, Pre), ll) ==>
	    \let sll = to_logic_list{Pre}(\at(*list, Pre), \at(previtem->next, Pre)) ;
	    \forall integer i ; 0 <= i < \length(sll) ==>
	      (\valid{Pre}(\at(\nth(sll, i), Pre)) && \valid{AR}(\at(\nth(sll, i), AR)) &&
	      \at(\nth(sll, i)->next, Pre) == \at(\nth(sll, i)->next, AR)) ;	      
	  */
	}
	/*@ assert in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	  in_list(previtem, to_logic_list{Pre}(\at(*list, Pre), newitem)) ==>
	  linked_ll{Pre}(\at(*list, Pre), \at(previtem->next, Pre), 
	              to_logic_list{Pre}(\at(*list, Pre), \at(previtem->next, Pre))) ;
	*/
      }

      /*@ assigns \nothing ;
	ensures in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	in_list(previtem, to_logic_list{Pre}(newitem, NULL)) ==>
	to_logic_list{AR}(\at(previtem->next, AR), NULL) == 
	to_logic_list{Pre}(\at(previtem->next, Pre), NULL) ;
      */ {
	/*@ assigns \nothing ;
	  ensures in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	  in_list(previtem, to_logic_list{Pre}(newitem, NULL)) ==>
	  (to_logic_list{AR}(\at(*list, AR), \at(previtem->next, AR)) ^
	   to_logic_list{AR}(\at(previtem->next, AR), NULL))
	   ==
	  (to_logic_list{Pre}(\at(*list, Pre), newitem) ^
	   to_logic_list{Pre}(\at(newitem->next, Pre), \at(previtem->next, AR)) ^
	   to_logic_list{Pre}(\at(previtem->next, AR), NULL)) ;
	*/ {
	  /*@ assert in_list(previtem, to_logic_list{Pre}(newitem, NULL)) ==>
	    in_list(\at(previtem->next, AR), to_logic_list{AR}(\at(*list, AR), NULL)) || 
	    \at(previtem->next, AR) == NULL ;
	  */
	  /*@ assert in_list(previtem, to_logic_list{Pre}(newitem, NULL)) ==>
	    linked_ll(\at(*list, AR), NULL, to_logic_list{AR}(\at(*list, AR), NULL)) ;
	  */
	  /*@ assert in_list(previtem, to_logic_list{Pre}(newitem, NULL)) ==>
	    to_logic_list{AR}(\at(*list, AR), NULL) ==
	    (to_logic_list{AR}(\at(*list, AR), \at(previtem->next, AR)) ^
	    to_logic_list{AR}(\at(previtem->next, AR), NULL)) ;
	  */
	  /*@ assert in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	    to_logic_list{AR}(\at(*list, AR), NULL) ==
	    (to_logic_list{Pre}(\at(*list, Pre), newitem) ^
	    to_logic_list{Pre}(\at(newitem->next, Pre), NULL)) ;
	  */
	  /*@ assert in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	    in_list(\at(previtem->next, Pre), to_logic_list{Pre}(\at(newitem->next, Pre), NULL)) ==>
	    to_logic_list{Pre}(\at(newitem->next, Pre), NULL) ==
	    (to_logic_list{Pre}(\at(newitem->next, Pre), \at(previtem->next, Pre)) ^
	    to_logic_list{Pre}(\at(previtem->next, Pre), NULL)) ;
	  */
	  /*@ assert in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	    \at(previtem->next, Pre) == NULL ==>
	    to_logic_list{Pre}(\at(newitem->next, Pre), NULL) ==
	    (to_logic_list{Pre}(\at(newitem->next, Pre), \at(previtem->next, Pre)) ^
	    to_logic_list{Pre}(\at(previtem->next, Pre), NULL)) ;
	  */
	  /*@ assert in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	    in_list(previtem, to_logic_list{Pre}(newitem, NULL)) ==>
	    in_list(\at(previtem->next, Pre), to_logic_list{Pre}(\at(newitem->next, Pre), NULL)) || 
	    \at(previtem->next, Pre) == NULL ;
	  */
	  /*@ assert in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	    in_list(previtem, to_logic_list{Pre}(newitem, NULL)) ==>
	    to_logic_list{Pre}(\at(newitem->next, Pre), NULL) ==
	    (to_logic_list{Pre}(\at(newitem->next, Pre), \at(previtem->next, Pre)) ^
	    to_logic_list{Pre}(\at(previtem->next, Pre), NULL)) ;
	  */
	}

	/*@ assigns \nothing ;
	    ensures in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	    in_list(\at(previtem->next, Pre), to_logic_list{Pre}(newitem->next, NULL)) ==>
	      unchanged{Pre, AR}(to_logic_list{Pre}(\at(previtem->next, Pre), NULL)) ;
	*/ {
	  /*@ assert in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	    \let ll = to_logic_list{Pre}(\at(newitem->next, Pre), NULL) ;
	    \forall integer i ; 0 <= i < \length(ll) ==> 
	    (\valid{Pre}(\at(\nth(ll, i), Pre)) && \valid{AR}(\at(\nth(ll, i), AR)) &&
	     \at(\nth(ll, i)->next, Pre) == \at(\nth(ll, i)->next, AR)) ;
	  */
	  /*@ assert in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	    linked_ll{Pre}(\at(newitem->next, Pre), NULL, to_logic_list(\at(newitem->next, Pre), NULL)) ;
	  */
	  /*@ assert in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	    in_list(\at(previtem->next, Pre), to_logic_list{Pre}(newitem->next, NULL)) ==>
	    to_logic_list{Pre}(\at(newitem->next, Pre), NULL) ==
	    (to_logic_list{Pre}(\at(newitem->next, Pre), \at(previtem->next, Pre)) ^ 
	     to_logic_list{Pre}(\at(previtem->next, Pre), NULL)) ;
	  */
	  /*@ assert in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	    \let ll = to_logic_list{Pre}(\at(newitem->next, Pre), NULL) ;
	    in_list(\at(previtem->next, Pre), ll) ==>
	    \let sll = to_logic_list{Pre}(\at(previtem->next, Pre), NULL) ;
	    \let left = to_logic_list{Pre}(\at(newitem->next, Pre), \at(previtem->next, Pre)) ;
	    \forall integer i ; 0 <= i < \length(sll) ==>
	    \let off_i = i + \length(left) ;
	    (\valid{Pre}(\at(\nth(ll, off_i), Pre)) && \valid{Pre}(\at(\nth(sll, i), Pre)) &&
	      \at(\nth(sll, i)->next, Pre) == \at(\nth(ll, off_i)->next, Pre)) ;
	  */
	  /*@ assert in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	    \let ll = to_logic_list{Pre}(\at(newitem->next, Pre), NULL) ;
	    in_list(\at(previtem->next, Pre), ll) ==>
	    \let sll = to_logic_list{Pre}(\at(previtem->next, Pre), NULL) ;
	      \length(sll) <= \length(ll) ;
	  */
	  /*@ assert in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	    \let ll = to_logic_list{Pre}(newitem->next, NULL) ;
	    in_list(\at(previtem->next, Pre), ll) ==>
	    \let sll = to_logic_list{Pre}(\at(previtem->next, Pre), NULL) ;
	    \forall integer i ; 0 <= i < \length(sll) ==>
	      (\valid{Pre}(\at(\nth(sll, i), Pre)) && \valid{AR}(\at(\nth(sll, i), AR)) &&
	      \at(\nth(sll, i)->next, Pre) == \at(\nth(sll, i)->next, AR)) ;	      
	  */
	}
	/*@ assert in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	  in_list(previtem, to_logic_list{Pre}(newitem->next, NULL)) ==>
	  linked_ll{Pre}(\at(previtem->next, Pre), NULL,
	              to_logic_list{Pre}(\at(previtem->next, Pre), NULL)) ;
	*/
	/* @ assert in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	  in_list(previtem, to_logic_list{Pre}(newitem->next, NULL)) ==>
	  \at(*list, Pre) == \at(*list, AR) ;
	*/
	/* @ assert in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	  in_list(previtem, to_logic_list{Pre}(newitem->next, NULL)) ==>
	  unchanged{Pre, AR}(to_logic_list{Pre}(\at(previtem->next, Pre), NULL)) ;
	*/
      }

      /*@ assigns \nothing ;
	ensures EASY_Right: in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	in_list(previtem, to_logic_list{Pre}(\at(*list, Pre), newitem)) ==>
	to_logic_list{AR}(\at(previtem->next, AR), NULL) == 
	(to_logic_list{Pre}(\at(previtem->next, Pre), newitem) ^ 
	 to_logic_list{Pre}(\at(newitem->next, Pre), NULL)) ;
      */ {
	/*@ assert in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	  in_list(previtem, to_logic_list{Pre}(\at(*list, Pre), newitem)) ==>
	  (to_logic_list{AR}(\at(*list, AR), \at(previtem->next, AR)) ^
	   to_logic_list{AR}(\at(previtem->next, AR), NULL))
	   ==
	  (to_logic_list{Pre}(\at(*list, Pre), \at(previtem->next, AR)) ^ 
	   to_logic_list{Pre}(\at(previtem->next, AR), newitem) ^
	   to_logic_list{Pre}(\at(newitem->next, Pre), NULL)) ;
	*/
	/*@ assert in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	  in_list(previtem, to_logic_list{Pre}(\at(*list, Pre), newitem)) ==>
	  to_logic_list{AR}(\at(*list, AR), \at(previtem->next, AR)) ==
	  to_logic_list{Pre}(\at(*list, Pre), \at(previtem->next, AR)) ;
	*/
	//@ assert \at(previtem->next, AR) == \at(previtem->next, Pre) ;
      }
      
      /*@ assigns \nothing ;
	ensures EASY_Left: in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	in_list(previtem, to_logic_list{Pre}(newitem, NULL)) ==>
	to_logic_list{AR}(\at(*list, AR), \at(previtem->next, AR)) == 
	(to_logic_list{Pre}(\at(*list, Pre), newitem) ^ 
	 to_logic_list{Pre}(\at(newitem->next, Pre), \at(previtem->next, Pre))) ;
      */ {
	/*@ assigns \nothing ;
	  ensures in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	  in_list(previtem, to_logic_list{Pre}(newitem, NULL)) ==>
	  (to_logic_list{AR}(\at(*list, AR), \at(previtem->next, AR)) ^
	   to_logic_list{AR}(\at(previtem->next, AR), NULL))
	   ==
	  (to_logic_list{Pre}(\at(*list, Pre), newitem) ^
	   to_logic_list{Pre}(\at(newitem->next, Pre), \at(previtem->next, AR)) ^
	   to_logic_list{Pre}(\at(previtem->next, AR), NULL)) ;
	*/ {
	  /*@ assert in_list(previtem, to_logic_list{Pre}(newitem, NULL)) ==>
	    in_list(\at(previtem->next, AR), to_logic_list{AR}(\at(*list, AR), NULL)) || 
	    \at(previtem->next, AR) == NULL ;
	  */
	  /*@ assert in_list(previtem, to_logic_list{Pre}(newitem, NULL)) ==>
	    linked_ll(\at(*list, AR), NULL, to_logic_list{AR}(\at(*list, AR), NULL)) ;
	  */
	  /*@ assert in_list(previtem, to_logic_list{Pre}(newitem, NULL)) ==>
	    to_logic_list{AR}(\at(*list, AR), NULL) ==
	    (to_logic_list{AR}(\at(*list, AR), \at(previtem->next, AR)) ^
	    to_logic_list{AR}(\at(previtem->next, AR), NULL)) ;
	  */
	  /*@ assert in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	    to_logic_list{AR}(\at(*list, AR), NULL) ==
	    (to_logic_list{Pre}(\at(*list, Pre), newitem) ^
	    to_logic_list{Pre}(\at(newitem->next, Pre), NULL)) ;
	  */
	  /*@ assert in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	    in_list(\at(previtem->next, Pre), to_logic_list{Pre}(\at(newitem->next, Pre), NULL)) ==>
	    to_logic_list{Pre}(\at(newitem->next, Pre), NULL) ==
	    (to_logic_list{Pre}(\at(newitem->next, Pre), \at(previtem->next, Pre)) ^
	    to_logic_list{Pre}(\at(previtem->next, Pre), NULL)) ;
	  */
	  /*@ assert in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	    \at(previtem->next, Pre) == NULL ==>
	    to_logic_list{Pre}(\at(newitem->next, Pre), NULL) ==
	    (to_logic_list{Pre}(\at(newitem->next, Pre), \at(previtem->next, Pre)) ^
	    to_logic_list{Pre}(\at(previtem->next, Pre), NULL)) ;
	  */
	  /*@ assert in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	    in_list(previtem, to_logic_list{Pre}(newitem, NULL)) ==>
	    in_list(\at(previtem->next, Pre), to_logic_list{Pre}(\at(newitem->next, Pre), NULL)) || 
	    \at(previtem->next, Pre) == NULL ;
	  */
	  /*@ assert in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	    in_list(previtem, to_logic_list{Pre}(newitem, NULL)) ==>
	    to_logic_list{Pre}(\at(newitem->next, Pre), NULL) ==
	    (to_logic_list{Pre}(\at(newitem->next, Pre), \at(previtem->next, Pre)) ^
	    to_logic_list{Pre}(\at(previtem->next, Pre), NULL)) ;
	  */
	}
	/*@ assert in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	  in_list(previtem, to_logic_list{Pre}(newitem, NULL)) ==>
	  to_logic_list{AR}(\at(previtem->next, AR), NULL) == 
	  to_logic_list{Pre}(\at(previtem->next, Pre), NULL) ;
	*/
      }

      
      list_force_insert(list, previtem, newitem);
    }
  }
}
/*---------------------------------------------------------------------------*/
/**
 * \brief      Get the next item following this item
 * \param item A list item
 * \returns    A next item on the list
 *
 *             This function takes a list item and returns the next
 *             item on the list, or NULL if there are no more items on
 *             the list. This function is used when iterating through
 *             lists.
 */
void *
list_item_next(void *item)
{
  return item == NULL ? NULL : ((struct list *)item)->next;
}
/*---------------------------------------------------------------------------*/
/**
 * \brief      Check if the list contains an item
 * \param list The list that is checked
 * \param item An item to look for in the list
 * \returns    0 if the list does not contains the item, and 1 otherwise
 *
 *             This function searches for an item in the list and returns 
 *			   0 if the list does not contain the item, and 1 if the item
 *			   is present in the list.
 */
bool
list_contains(list_t list, void *item)
{
  struct list *l;
  for(l = *list; l != NULL; l = l->next) {
    if(item == l) {
    	return true;
    }
  }
  return false;
}
/*---------------------------------------------------------------------------*/
/** @} */
