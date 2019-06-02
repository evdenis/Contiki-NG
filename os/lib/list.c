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
  *dest = *src;
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

  ((struct list *)item)->next = *list;
  *list = item;
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

  for(l = *list; l->next->next != NULL; l = l->next);

  r = l->next;
  l->next = NULL;

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
    *list = ((struct list *)*list)->next;
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
  struct list *l, *r;

  if(*list == NULL) {
    return;
  }

  r = NULL;
  for(l = *list; l != NULL; l = l->next) {
    if(l == item) {
      if(r == NULL) {
        /* First on list */
        *list = l->next;
      } else {
        /* Not first on list */
        r->next = l->next;
      }
      l->next = NULL;
      return;
    }
    r = l;
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
    list_remove(list, newitem);
    ((struct list *)newitem)->next = ((struct list *)previtem)->next;
    ((struct list *)previtem)->next = newitem;
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
/** @} */
