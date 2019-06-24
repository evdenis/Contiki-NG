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
 * Linked list manipulation routines.
 * \author Adam Dunkels <adam@sics.se>
 *
 */

/** \addtogroup data
    @{ */
/**
 * \defgroup list Linked list library
 *
 * The linked list library provides a set of functions for
 * manipulating linked lists.
 *
 * A linked list is made up of elements where the first element \b
 * must be a pointer. This pointer is used by the linked list library
 * to form lists of the elements.
 *
 * Lists are declared with the LIST() macro. The declaration specifies
 * the name of the list that later is used with all list functions.
 *
 * Lists can be manipulated by inserting or removing elements from
 * either sides of the list (list_push(), list_add(), list_pop(),
 * list_chop()). A specified element can also be removed from inside a
 * list with list_remove(). The head and tail of a list can be
 * extracted using list_head() and list_tail(), respectively.
 *
 * This library is not safe to be used within an interrupt context.
 * @{
 */

#ifndef LIST_H_
#define LIST_H_

#include <stdbool.h>

#define LIST_CONCAT2(s1, s2) s1##s2
#define LIST_CONCAT(s1, s2) LIST_CONCAT2(s1, s2)

/**
 * Declare a linked list.
 *
 * This macro declares a linked list with the specified \c type. The
 * type \b must be a structure (\c struct) with its first element
 * being a pointer. This pointer is used by the linked list library to
 * form the linked lists.
 *
 * The list variable is declared as static to make it easy to use in a
 * single C module without unnecessarily exporting the name to other
 * modules.
 *
 * \param name The name of the list.
 */
#define LIST(name) \
         static void *LIST_CONCAT(name,_list) = NULL; \
         static list_t name = (list_t)&LIST_CONCAT(name,_list)

/**
 * Declare a linked list inside a structure declaraction.
 *
 * This macro declares a linked list with the specified \c type. The
 * type \b must be a structure (\c struct) with its first element
 * being a pointer. This pointer is used by the linked list library to
 * form the linked lists.
 *
 * Internally, the list is defined as two items: the list itself and a
 * pointer to the list. The pointer has the name of the parameter to
 * the macro and the name of the list is a concatenation of the name
 * and the suffix "_list". The pointer must point to the list for the
 * list to work. Thus the list must be initialized before using.
 *
 * The list is initialized with the LIST_STRUCT_INIT() macro.
 *
 * \param name The name of the list.
 */
#define LIST_STRUCT(name) \
         void *LIST_CONCAT(name,_list); \
         list_t name

/**
 * Initialize a linked list that is part of a structure.
 *
 * This macro sets up the internal pointers in a list that has been
 * defined as part of a struct. This macro must be called before using
 * the list.
 *
 * \param struct_ptr A pointer to the struct
 * \param name The name of the list.
 */
#define LIST_STRUCT_INIT(struct_ptr, name)                              \
    do {                                                                \
       (struct_ptr)->name = &((struct_ptr)->LIST_CONCAT(name,_list));   \
       (struct_ptr)->LIST_CONCAT(name,_list) = NULL;                    \
       list_init((struct_ptr)->name);                                   \
    } while(0)

#ifdef SPECIFICATION
# include "list_logic_defs.spec"
# include "list_lemmas.spec"
# include "list_split.c"
# include "list_force_insert.c"
#endif

/**
 * The linked list type.
 *
 */
typedef void ** list_t;

/*@ requires \valid(list);
  @ 
  @ assigns *list ;
  @ 
  @ ensures ValidHandler:  \valid(list);
  @ ensures HandlerSep:    dptr_separated_from_list(list, to_logic_list(*list, NULL));
  @ ensures Linked:         linked_ll(*list, NULL, to_logic_list(*list, NULL));
  @ ensures LengthMax:     \length(to_logic_list(*list, NULL)) < INT_MAX ;
  @
  @ ensures *list == NULL;
  @ ensures to_logic_list(*list, NULL) == \Nil ;
  @ ensures linked_ll(*list, NULL, \Nil);
  @*/
void   list_init(list_t list);
/*@ requires ValidHandler: \valid(list);
  @ requires HandlerSep:   dptr_separated_from_list(list, to_logic_list(*list, NULL));
  @ requires Linked:        linked_ll(*list, NULL, to_logic_list(*list, NULL));
  @ requires LengthMax:    \length(to_logic_list(*list, NULL)) < INT_MAX ;
  @ 
  @ assigns \nothing ;
  @
  @ ensures ValidHandler:  \valid(list);
  @ ensures HandlerSep:    dptr_separated_from_list(list, to_logic_list(*list, NULL));
  @ ensures Linked:         linked_ll(*list, NULL, to_logic_list(*list, NULL));
  @ ensures LengthMax:     \length(to_logic_list(*list, NULL)) < INT_MAX ;
  @ 
  @ behavior empty:
  @   assumes *list == NULL;
  @   ensures \result == NULL;
  @   
  @ behavior not_empty:
  @   assumes *list != NULL;
  @   ensures \result == \nth(to_logic_list(*list, NULL), 0);
  @
  @ complete behaviors;
  @ disjoint behaviors;
*/
void * list_head(list_t list);
/*@ requires ValidHandler: \valid(list);
  @ requires HandlerSep:   dptr_separated_from_list(list, to_logic_list(*list, NULL));
  @ requires Linked:        linked_ll(*list, NULL, to_logic_list(*list, NULL));
  @ requires LengthMax:    \length(to_logic_list(*list, NULL)) < INT_MAX ;
  @ 
  @ assigns \nothing ;
  @
  @ ensures HandlerSep:    dptr_separated_from_list(list, to_logic_list(*list, NULL));
  @ ensures ValidHandler:  \valid(list);
  @ ensures Linked:         linked_ll(*list, NULL, to_logic_list(*list, NULL));
  @ ensures LengthMax:     \length(to_logic_list(*list, NULL)) < INT_MAX ;
  @
  @ behavior empty:
  @   assumes *list == NULL;
  @   ensures \result == NULL;
  @
  @ behavior not_empty:
  @   assumes *list != NULL;
  @   ensures \let ll = to_logic_list(*list, NULL) ; \result == \nth(ll, \length(ll)-1);
  @
  @ complete behaviors;
  @ disjoint behaviors;
  @*/
void * list_tail(list_t list);
/*@ requires ValidHandler: \valid(list);
  @ requires HandlerSep:   dptr_separated_from_list(list, to_logic_list(*list, NULL));
  @ requires Linked:        linked_ll(*list, NULL, to_logic_list(*list, NULL));
  @ requires LengthMax:    \length(to_logic_list(*list, NULL)) < INT_MAX ;
  @ 
  @ assigns *list ;
  @
  @ ensures HandlerSep:   dptr_separated_from_list(list, to_logic_list(*list, NULL));
  @ ensures ValidHandler: \valid(list);
  @ ensures Linked:        linked_ll(*list, NULL, to_logic_list(*list, NULL));
  @ ensures RemovedHead:  ptr_separated_from_list(\old(*list), to_logic_list(*list, NULL));
  @ 
  @ behavior empty:
  @   assumes *list  == NULL ;
  @   ensures \result == NULL ;
  @   
  @ behavior not_empty:
  @   assumes *list != NULL ;
  @   ensures \result == \old(*list) ;
  @   ensures *list == \old((*list)->next) ;
  @   ensures to_logic_list{Pre}(\at(*list, Pre), NULL) ==
  @           ([| \at(*list, Pre) |] ^ to_logic_list(*list, NULL));
  @   ensures \length(to_logic_list(*list, NULL)) ==
  @           \length(to_logic_list{Pre}(\at(*list,Pre), NULL)) - 1 ;
  @           
  @ complete behaviors;
  @ disjoint behaviors;
  @*/
void * list_pop (list_t list);
/*@ requires ValidHandler: \valid(list);
  @ requires HandlerSep:   dptr_separated_from_list(list, to_logic_list(*list, NULL));
  @ requires Linked:        linked_ll(*list, NULL, to_logic_list(*list, NULL));
  @ requires LengthMax:    \length(to_logic_list(*list, NULL)) < INT_MAX ;
  @ requires \valid(item) && \separated(list, item);
  @ requires in_list(item, to_logic_list(*list, NULL)) ||
  @          ptr_separated_from_list(item, to_logic_list(*list, NULL)) ;
  @
  @ ensures HandlerSep:    dptr_separated_from_list(list, to_logic_list(*list, NULL));
  @ ensures ValidHandler:  \valid(list);
  @ ensures Linked:         linked_ll(*list, NULL, to_logic_list(*list, NULL));
  @ ensures First:         *list == item ;
  @
  @ assigns *list,
  @         item->next,
  @         { l->next 
  @           | struct list* l ; 
  @             in_list(l, to_logic_list{Pre}(\at(*list, Pre), NULL)) && 
  @             \at(l->next, Pre) == item } ;
  @
  @ behavior does_not_contain:
  @   assumes ! in_list(item, to_logic_list(*list, NULL)) ;
  @   ensures AddedBegin: to_logic_list(*list, NULL) ==
  @                     ([| item |] ^ to_logic_list{Pre}(\old(*list), NULL)) ;
  @   ensures SizeInc: \length(to_logic_list(*list, NULL)) == 
  @                    \length(to_logic_list{Pre}(\at(*list,Pre), NULL)) + 1 ;
  @
  @ behavior contains:
  @   assumes in_list(item, to_logic_list(*list, NULL)) ;
  @   ensures NewList: to_logic_list(*list, NULL) ==
  @     ([| item |] ^ to_logic_list{Pre}(\old(*list), item) ^ 
  @      to_logic_list{Pre}(\at(item->next,Pre), NULL)) ;
  @   ensures SameSize: \length(to_logic_list(*list, NULL)) == 
  @                     \length(to_logic_list{Pre}(\at(*list,Pre), NULL)) ;
  @           
  @ complete behaviors;
  @ disjoint behaviors;
*/
void   list_push(list_t list, void *item);
/*@ requires ValidHandler: \valid(list);
  @ requires HandlerSep:   dptr_separated_from_list(list, to_logic_list(*list, NULL));
  @ requires Linked:        linked_ll(*list, NULL, to_logic_list(*list, NULL));
  @ requires LengthMax:    \length(to_logic_list(*list, NULL)) < INT_MAX ;
  @
  @ ensures HandlerSep:    dptr_separated_from_list(list, to_logic_list(*list, NULL));
  @ ensures ValidHandler:  \valid(list);
  @ ensures Linked:         linked_ll(*list, NULL, to_logic_list(*list, NULL));
  @
  @ assigns *list,
  @         { l->next 
  @           | struct list* l ; 
  @             in_list(l, to_logic_list{Pre}(\at(*list, Pre), NULL)) && 
  @             \at(l->next, Pre) != NULL && \at(l->next->next, Pre) == NULL } ;
  @
  @ behavior empty:
  @   assumes *list == NULL ;
  @   assigns \nothing ;
  @   ensures *list == \old(*list);
  @   ensures RemainsNull: *list == NULL ;
  @   ensures Nothing: \result == NULL ;
  @
  @ behavior single_element:
  @   assumes *list != NULL ;
  @   assumes (*list)->next == NULL ;
  @   assigns *list ;
  @   ensures NowNull: *list == NULL ;
  @   ensures Head: \result == \old(*list) ;
  @
  @ behavior more_elements:
  @   assumes *list != NULL && (*list)->next != NULL ;
  @   assigns 
  @     \nth(to_logic_list{Pre}(*list, NULL), \length(to_logic_list{Pre}(*list, NULL)) - 2)->next;
  @   ensures *list == \old(*list);
  @   ensures NewList:
  @     \let pre_ll = to_logic_list{Pre}(*list, NULL) ;
  @     to_logic_list(*list, NULL) ==
  @     to_logic_list{Pre}(\at(*list, Pre), \nth(pre_ll, \length(pre_ll)-1)) ;
  @   ensures Tail:
  @     \let pre_ll = to_logic_list{Pre}(*list, NULL) ;
  @     \result == \nth(pre_ll, \length(pre_ll) - 1) ;
  @
  @ complete behaviors ;
  @ disjoint behaviors ;
*/
void * list_chop(list_t list);
/*@ requires ValidHandler: \valid(list);
  @ requires HandlerSep:   dptr_separated_from_list(list, to_logic_list(*list, NULL));
  @ requires Linked:        linked_ll(*list, NULL, to_logic_list(*list, NULL));
  @ requires LengthMax:    \length(to_logic_list(*list, NULL)) < INT_MAX ;
  @ requires \valid(item) && \separated(list, item);
  @ requires in_list(item, to_logic_list(*list, NULL)) ||
  @          ptr_separated_from_list(item, to_logic_list(*list, NULL)) ;
  @
  @ ensures HandlerSep:    dptr_separated_from_list(list, to_logic_list(*list, NULL));
  @ ensures ValidHandler:  \valid(list);
  @ ensures Linked:         linked_ll(*list, NULL, to_logic_list(*list, NULL));
  @
  @ assigns *list,
  @         item->next,
  @         { l->next 
  @           | struct list* l ; 
  @             in_list(l, to_logic_list{Pre}(\at(*list, Pre), NULL)) && 
  @             (\at(l->next, Pre) == NULL || \at(l->next, Pre) == item) } ;
  @
  @ behavior does_not_contain:
  @   assumes ! in_list(item, to_logic_list(*list, NULL)) ;
  @   ensures \old(*list) != NULL ==> *list == \old(*list) ;
  @   ensures \old(*list) == NULL ==> *list == item ;
  @   ensures AddedEnd: to_logic_list(*list, NULL) == 
  @                     (to_logic_list{Pre}(\old(*list), NULL) ^ [| item |]) ;
  @   ensures SizeInc: \length(to_logic_list(*list, NULL)) == 
  @                    \length(to_logic_list{Pre}(\at(*list,Pre), NULL)) + 1 ;
  @
  @ behavior contains:
  @   assumes in_list(item, to_logic_list(*list, NULL)) ;
  @   ensures NewList: to_logic_list(*list, NULL) ==
  @     (to_logic_list{Pre}(\old(*list), item) ^ 
  @      to_logic_list{Pre}(\at(item->next, Pre), NULL) ^ [| item |] ) ;
  @   ensures SameSize: \length(to_logic_list(*list, NULL)) == 
  @                     \length(to_logic_list{Pre}(\at(*list,Pre), NULL)) ;
  @           
  @ complete behaviors;
  @ disjoint behaviors;
*/
void   list_add(list_t list, void *item);
/*@ requires ValidHandler: \valid(list);
  @ requires HandlerSep:   dptr_separated_from_list(list, to_logic_list(*list, NULL));
  @ requires Linked:        linked_ll(*list, NULL, to_logic_list(*list, NULL));
  @ requires LengthMax:    \length(to_logic_list(*list, NULL)) < INT_MAX ;
  @ requires \valid(item) ;
  @ requires in_list(item, to_logic_list(*list, NULL)) ||
  @          ptr_separated_from_list(item, to_logic_list(*list, NULL)) ;
  @
  @ ensures ValidHandler:  \valid(list);
  @ ensures HandlerSep:    dptr_separated_from_list(list, to_logic_list(*list, NULL));
  @ ensures Linked:         linked_ll(*list, NULL, to_logic_list(*list, NULL));
  @ ensures ItemUnchanged: item->next == \old(item->next) && \valid(item);
  @ ensures ItemNotIn:     ptr_separated_from_list(item, to_logic_list(*list, NULL));
  @ ensures AllOthers:    \forall struct list* l ; l != item ==> (
  @                          in_list(l, to_logic_list{Pre}(\old(*list), NULL)) <==>
  @                            in_list(l, to_logic_list(*list, NULL)));
  @ 
  @ assigns *list,
  @         { l->next 
  @           | struct list* l ; 
  @             in_list(l, to_logic_list{Pre}(\at(*list, Pre), NULL)) && 
  @             \at(l->next, Pre) == item } ;
  @
  @ behavior does_not_contain:
  @   assumes ! in_list(item, to_logic_list(*list, NULL)) ;
  @   ensures *list == \old(*list) ;
  @   ensures SameList:  to_logic_list{Pre}(\old(*list), NULL) == to_logic_list(*list, NULL) ;
  @   ensures SameSize: \length(to_logic_list(*list, NULL)) == 
  @                     \length(to_logic_list{Pre}(\at(*list,Pre), NULL)) ;
  @
  @ behavior contains:
  @   assumes in_list(item, to_logic_list(*list, NULL)) ;
  @   ensures \old(*list) == item ==> *list == \old(item->next) ;
  @   ensures \old(*list) != item ==> *list == \old(*list) ;
  @   ensures Link: \forall struct list* e ; 
  @     (in_list(e, to_logic_list{Pre}(\at(*list, Pre), NULL)) && \at(e->next, Pre) == item) ==> 
  @       e->next == item->next ;
  @       
  @   ensures NewList:
  @     (to_logic_list{Pre}(\old(*list), item) ^ to_logic_list{Pre}(item->next, NULL)) ==
  @       to_logic_list(*list, NULL) ;
  @   ensures SizeReduced: \length(to_logic_list(*list, NULL)) == 
  @                        \length(to_logic_list{Pre}(\at(*list,Pre), NULL)) - 1 ;
  @           
  @ complete behaviors;
  @ disjoint behaviors;
  @*/
void   list_remove(list_t list, void *item);
/*@ requires ValidHandler: \valid(list);
  @ requires HandlerSep:   dptr_separated_from_list(list, to_logic_list(*list, NULL));
  @ requires Linked:        linked_ll(*list, NULL, to_logic_list(*list, NULL));
  @ requires LengthMax:    \length(to_logic_list(*list, NULL)) < INT_MAX ;
  @ 
  @ assigns \nothing ;
  @
  @ ensures \result == \length(to_logic_list(*list, NULL));
  @*/
int    list_length(list_t list);
/*@ requires ValidHandler: \valid(src);
  @ requires HandlerSep: dptr_separated_from_list(src, to_logic_list(*src, NULL));
  @ requires Linked: linked_ll(*src, NULL, to_logic_list(*src, NULL));
  @ requires LengthMax: \length(to_logic_list(*src, NULL)) < INT_MAX ;
  @
  @ requires \valid(dest) ;
  @ requires dptr_separated_from_list(dest, to_logic_list(*src, NULL));
  @
  @ assigns *dest ;
  @ 
  @ ensures HandlerSep1:  dptr_separated_from_list(src, to_logic_list(*src, NULL));
  @ ensures HandlerSep2:  dptr_separated_from_list(dest, to_logic_list(*src, NULL));
  @ ensures LengthMax:    \length(to_logic_list(*src, NULL)) < INT_MAX ;
  @ ensures ValidHandler: \valid(src) && \valid(dest);
  @ ensures Linked:        linked_ll(*src, NULL, to_logic_list(*src, NULL));
  @ ensures unchanged{Pre,Here}(to_logic_list{Pre}(*src, NULL));
  @ ensures linked_ll(*dest, NULL, to_logic_list(*dest, NULL));
  @ ensures to_logic_list(*dest, NULL) == to_logic_list{Pre}(*src, NULL) ;
  @*/
void   list_copy(list_t dest, list_t src);
/*@ requires ValidHandler: \valid(list);
  @ requires HandlerSep:   dptr_separated_from_list(list, to_logic_list(*list, NULL));
  @ requires Linked:        linked_ll(*list, NULL, to_logic_list(*list, NULL));
  @ requires LengthMax:    \length(to_logic_list(*list, NULL)) < INT_MAX ;
  @ requires \valid(newitem) ;
  @ requires previtem == NULL || in_list(previtem, to_logic_list(*list, NULL)) ;
  @ requires in_list(newitem, to_logic_list(*list, NULL)) ||
  @          ptr_separated_from_list(newitem, to_logic_list(*list, NULL)) ;
  @ requires \separated(list, previtem, newitem) ;
  @
  @ ensures HandlerSep:    dptr_separated_from_list(list, to_logic_list(*list, NULL));
  @ ensures ValidHandler:  \valid(list);
  @ ensures Linked:         linked_ll(*list, NULL, to_logic_list(*list, NULL));
  @
  @ assigns *list,
  @         newitem->next,
  @         previtem->next,
  @         { l->next | struct list* l ; in_list(l, to_logic_list{Pre}(*list, NULL)) } ;
  @
  @ behavior at_beginning_and_does_not_contain:
  @   assumes previtem == NULL ;
  @   assumes !in_list(newitem, to_logic_list{Pre}(*list, NULL));
  @   ensures AddedBegin: to_logic_list(*list, NULL) ==
  @                     ([| newitem |] ^ to_logic_list{Pre}(\old(*list), NULL)) ;
  @   ensures SizeInc: \length(to_logic_list(*list, NULL)) == 
  @                    \length(to_logic_list{Pre}(\at(*list,Pre), NULL)) + 1 ;
  @
  @ behavior at_beginning_and_contains:
  @   assumes previtem == NULL ;
  @   assumes in_list(newitem, to_logic_list{Pre}(*list, NULL));
  @   ensures NewList: to_logic_list(*list, NULL) ==
  @     ([| newitem |] ^ to_logic_list{Pre}(\old(*list), newitem) ^ 
  @      to_logic_list{Pre}(\at(newitem->next,Pre), NULL)) ;
  @   ensures SameSize: \length(to_logic_list(*list, NULL)) == 
  @                     \length(to_logic_list{Pre}(\at(*list,Pre), NULL)) ;
  @
  @ behavior somewhere_else_does_not_contain:
  @   assumes previtem != NULL ;
  @   assumes !in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL));
  @   ensures NewList: to_logic_list(*list, NULL) == (
  @     to_logic_list{Pre}(\old(*list), \old(previtem->next)) ^
  @     [| newitem |] ^
  @     to_logic_list{Pre}(\old(previtem->next), NULL));
  @   ensures SizeInc: \length(to_logic_list(*list, NULL)) == 
  @                    \length(to_logic_list{Pre}(\at(*list,Pre), NULL)) + 1 ;
  @
  @ behavior somewhere_else_contains_after_prev_linked:
  @   assumes previtem != NULL ;
  @   assumes in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL));
  @   assumes in_list(previtem, to_logic_list{Pre}(\at(*list, Pre), newitem)) ;
  @   assumes \at(previtem->next, Pre) == newitem ;
  @   ensures NewList: to_logic_list(*list, NULL) == to_logic_list{Pre}(\at(*list, Pre), NULL) ;
  @   ensures SameSize: \length(to_logic_list(*list, NULL)) == 
  @                     \length(to_logic_list{Pre}(\at(*list,Pre), NULL)) ;
  @
  @ behavior somewhere_else_contains_after_prev_not_linked:
  @   assumes previtem != NULL ;
  @   assumes in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL));
  @   assumes in_list(previtem, to_logic_list{Pre}(\at(*list, Pre), newitem)) ;
  @   assumes \at(previtem->next, Pre) != newitem ;
  @   ensures NewList: to_logic_list(*list, NULL) == 
  @     (to_logic_list{Pre}(\at(*list, Pre), \at(previtem->next, Pre)) ^ 
  @     [| newitem |] ^
  @     to_logic_list{Pre}(\at(previtem->next, Pre), newitem) ^
  @     to_logic_list{Pre}(\at(newitem->next, Pre), NULL)) ;
  @   ensures SameSize: \length(to_logic_list(*list, NULL)) == 
  @                     \length(to_logic_list{Pre}(\at(*list,Pre), NULL)) ;
  @
  @ behavior somewhere_else_contains_before:
  @   assumes previtem != NULL ;
  @   assumes in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL));
  @   assumes in_list(previtem, to_logic_list{Pre}(newitem, NULL));
  @   ensures NewList: to_logic_list(*list, NULL) == 
  @     (to_logic_list{Pre}(\at(*list, Pre), newitem) ^ 
  @     to_logic_list{Pre}(\at(newitem->next, Pre), \at(previtem->next, Pre)) ^
  @     [| newitem |] ^
  @     to_logic_list{Pre}(\at(previtem->next, Pre), NULL)) ;
  @   ensures SameSize: \length(to_logic_list(*list, NULL)) == 
  @                     \length(to_logic_list{Pre}(\at(*list,Pre), NULL)) ;
  @
  @ complete behaviors;
  @ disjoint behaviors;
*/
void   list_insert(list_t list, void *previtem, void *newitem);
/*@ requires linked_ll(item, NULL, to_logic_list(item, NULL));
  @ 
  @ assigns \nothing ;
  @
  @ behavior empty:
  @   assumes item == NULL ;
  @   ensures \result == NULL ;
  @   
  @ behavior not_empty:
  @   assumes item != NULL ;
  @   ensures \result == item->next ;
  @   ensures linked_ll(item->next, NULL, to_logic_list(item->next, NULL));
  @   ensures to_logic_list(item, NULL) ==
  @           ([| item |] ^ to_logic_list(item->next, NULL)) ;
  @           
  @ complete behaviors;
  @ disjoint behaviors;
  @*/
void * list_item_next(void *item);

bool list_contains(list_t list, void *item);

#endif /* LIST_H_ */

/** @} */
/** @} */
