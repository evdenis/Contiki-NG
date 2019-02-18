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
 * @{
 */

#ifndef LIST_H_
#define LIST_H_

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

#include "lib/spec_list.h"

/**
 * The linked list type.
 *
 */
typedef void ** list_t;

/*@
  requires \valid(list);
  requires ValidArray : \valid( array + (0 .. MAX_SIZE - 1) );

  requires GhostSeparation:
    \separated(list, array + (0 .. MAX_SIZE - 1)) ;
  requires 
    \separated(*list, array + (0 .. MAX_SIZE - 1)) ;

  assigns  *list ;

  ensures ValidArray : \valid( array + (0 .. MAX_SIZE - 1) );

  ensures GhostSeparation:
    \separated(list, array + (0 .. MAX_SIZE - 1)) ;
  ensures 
    \separated(*list, array + (0 .. MAX_SIZE - 1)) ;

  ensures  linked_n(*list, array, 0, 0, *list);
  ensures  *list == NULL;
*/
void   list_init(list_t list);
/*@
  requires \valid(list);
  requires linked_n(*list, array, index, n, NULL);
  assigns \nothing ;

  behavior empty:
    assumes *list == NULL;
    ensures \result == NULL;

  behavior not_empty:
    assumes *list != NULL;
    ensures \result == array[index];
 */
void * list_head(list_t list);
/*@
  requires \valid(list);
  requires ValidArray : \valid( array + (0 .. MAX_SIZE - 1) );
  requires linked_n(*list, array, index, n, NULL);
  assigns \nothing ;

  behavior empty:
    assumes *list == NULL;
    ensures \result == NULL;

  behavior not_empty:
    assumes *list != NULL;
    ensures \result == array[index+n-1];
    ensures \result != NULL;
    ensures linked_n(*list, array, index, n-1, \result);
  
  complete behaviors;
  disjoint behaviors;
 */
void * list_tail(list_t list);
/*@
  requires \valid(list);
  requires Linked : linked_n (*list, array, index, n, NULL);
  requires ValidArray : \valid( array + (0 .. MAX_SIZE - 1) );
  requires 0 <= index ;

  requires GhostSeparation:
    \separated(list, array + (0 .. MAX_SIZE - 1)) ;
  requires 
    \separated(list, *(array + (index .. index + n - 1))) ;
  requires 
    \separated(*list, array + (0 .. MAX_SIZE - 1)) ;

  requires Separation:
    \forall integer y ; 
      index <= y < index + n ==> 
        \separated( * (array + y), array + (0 .. MAX_SIZE - 1));

  requires Separation:
    \forall integer y, z; 
      index <= y < index + n && index <= z < index + n && y != z ==> 
        \separated(* (array+y), *(array+z));

  requires Unique:
    \forall integer y, z; 
      index <= y < index + n && index <= z < index + n && y != z ==> 
        array[y] != array[z];

  ensures \result == \at(*list, Pre);

  ensures GhostSeparation:
    \separated(list, array + (0 .. MAX_SIZE - 1)) ;
  ensures 
    \separated(list, *(array + (index .. index + n - 1))) ;
  ensures 
    \separated(*list, array + (0 .. MAX_SIZE - 1)) ;

  behavior empty :
    assumes n == 0;

    ensures *list == \at(*list, Pre);
    ensures linked_n (*list, array, index, n, NULL);
    ensures unchanged{Pre, Post} (array, index, index + n);
    ensures \result == \null;

    ensures Unique:
      \forall integer y, z; 
        index <= y < index + n && index <= z < index + n && y != z ==> 
          array[y] != array[z];

    ensures Separation:
      \forall integer y ; 
        index <= y < index + n ==> 
          \separated( * (array + y), array + (0 .. MAX_SIZE - 1));

    ensures Separation:
      \forall integer y, z; 
        index <= y < index + n && index <= z < index + n && y != z ==> 
          \separated(* (array+y), *(array+z));
    
    assigns \nothing;


  behavior more:
    assumes n >= 1;

    ensures *list == \at((*list)->next, Pre);
    ensures array_swipe_left{Pre, Post} (array, index, index + n - 1);
    ensures linked_n (*list, array, index, n - 1, NULL);
    
    ensures Unique:
      \forall integer y, z; 
        index <= y < index + n - 1 && index <= z < index + n - 1 && y != z ==> 
          array[y] != array[z];

    ensures Separation : 
      \forall integer y; 
        index <= y < index + n - 1 ==> 
          \separated( * (array + y), array + (0 .. MAX_SIZE - 1));

    ensures Separation:
      \forall integer y, z; 
        index <= y < index + n - 1 && index <= z < index + n - 1 && y != z ==> 
          \separated(* (array+y), *(array+z));

    ensures NoMoreHere:
      \forall integer x ; index <= x < index+n-1 ==> array[x] != \result ;

    ensures NoMoreHere:
      \forall integer x ; index <= x < index+n-1 ==> \separated(array[x], \result);


    assigns *list, array[index .. index + n-2];
        
  complete behaviors;
  disjoint behaviors;
*/
void * list_pop (list_t list);
/*@
  requires \valid( list ) && \valid(item) ;
  requires \separated(list, item) ;
  requires Linked : linked_n (*list, array, index, n, NULL);
  requires ValidArray : \valid(array + (0 .. MAX_SIZE-1));
  requires 0 <= index && 0 <= n < MAX_SIZE ;
  requires EnoughSpace : index + n + 1 <= MAX_SIZE; 

  requires GhostSeparation: \separated(list, array + (0 .. MAX_SIZE - 1)) ;
  requires GhostSeparation: \separated(list, *(array + (index .. index + n - 1))) ;
  requires GhostSeparation: \separated(*list, array + (0 .. MAX_SIZE - 1)) ;

  requires \separated(item, array + (0 .. MAX_SIZE - 1)) ;
  requires Item_Separation:
    \forall integer i ; index <= i < index + n ==> 
      item != array[i] ==> \separated(item, array[i]);

  requires Separation: 
    \forall integer y ; 
      index <= y < index + n ==> 
        \separated( * (array + y), array + (0 .. MAX_SIZE - 1));

  requires Separation : 
    \forall integer y, z; 
      index <= y < index + n && index <= z < index + n && y != z ==> 
        \separated( * (array + y), * (array + z) );

  requires Unique:
    \forall integer y, z; 
      index <= y < index + n && index <= z < index + n && y != z ==> 
        array[y] != array[z];

  requires item_idx == index_of(item, array, index, index+n) ;

  assigns array[index .. index + n], array[item_idx - 1]->next, 
          item->next, *list ;

  ensures GhostSeparation: \separated(list, array + (0 .. MAX_SIZE - 1)) ;
  ensures GhostSeparation: \separated(*list, array + (0 .. MAX_SIZE - 1)) ;

  behavior contains_item:
    assumes \exists integer i ; index <= i < index+n && array[i] == item ;
    ensures linked_n(*list, array, index, n, NULL);
    ensures unchanged{Pre,Post}(array, item_idx + 1, index+n);
    ensures array_swipe_right{Pre, Post}(array, index + 1, item_idx + 1);
    ensures array[index] == item ;

    ensures GhostSeparation: \separated(list, *(array + (index .. index + n - 1))) ;

    ensures Separation : 
      \forall integer y ; index <= y < index + n  ==> 
          \separated( * (array + y), array + (0 .. MAX_SIZE - 1));

    ensures Separation : 
      \forall integer y, z; 
        index <= y < index + n && index <= z < index + n && y != z ==> 
          \separated( * (array + y), * (array + z) );

    ensures Unique:
      \forall integer y, z; 
        index <= y < index + n && index <= z < index + n && y != z ==> 
          array[y] != array[z];

  behavior does_not_contain_item:
    assumes \forall integer i ; index <= i < index+n ==> array[i] != item ;
    ensures linked_n(*list, array, index, n+1, NULL);
    ensures array_swipe_right{Pre, Post}(array, index + 1, index + n + 1);
    ensures array[index] == item ;

    ensures GhostSeparation: \separated(list, *(array + (index .. index + n))) ;

    ensures Separation : 
      \forall integer y ; index <= y < index + n + 1 ==> 
          \separated( * (array + y), array + (0 .. MAX_SIZE - 1));

    ensures Separation : 
      \forall integer y, z; 
        index <= y < index + n + 1 && index <= z < index + n + 1 && y != z ==> 
          \separated( * (array + y), * (array + z) );

    ensures Unique:
      \forall integer y, z; 
        index <= y < index + n + 1 && index <= z < index + n + 1 && y != z ==> 
          array[y] != array[z];
  
  complete behaviors ;
  disjoint behaviors ;
*/
void   list_push(list_t list, void *item);

/*@
  requires \valid(list);
  requires \valid(array + (0 .. MAX_SIZE - 1));
  requires linked_n(*list, array, index, size, NULL);
  
  requires GhostSeparation: \separated(list, array + (0 .. MAX_SIZE - 1)) ;
  requires GhostSeparation: \separated(list, *(array + (index .. index + size - 1))) ;
  requires GhostSeparation: \separated(*list, array + (0 .. MAX_SIZE - 1)) ;

  requires Separation : 
    \forall integer y ; 
      index <= y < index + size ==> 
        \separated( * (array + y), array + (0 .. MAX_SIZE - 1));

  requires Separation:
    \forall integer y, z; 
      index <= y < index + size && index <= z < index + size && y != z ==> 
        \separated(* (array+y), *(array+z));

  requires Unique:
    \forall integer y, z; 
      index <= y < index + size && index <= z < index + size && y != z ==> 
        array[y] != array[z];

  assigns *list, array[index+size-2]->next ;
  
  ensures GhostSeparation: \separated(list, array + (0 .. MAX_SIZE - 1)) ;
  ensures GhostSeparation: \separated(list, *(array + (index .. index + size - 1))) ;
  ensures GhostSeparation: \separated(*list, array + (0 .. MAX_SIZE - 1)) ;

  ensures unchanged{Pre, Here}(array, index, index + size - 2);

  ensures Separation : 
    \forall integer y ; 
      index <= y < index + size - 1 ==> 
        \separated( * (array + y), array + (0 .. MAX_SIZE - 1));

  ensures Separation:
    \forall integer y, z; 
      index <= y < index + size - 1 && index <= z < index + size - 1 && y != z ==> 
        \separated(* (array+y), *(array+z));

  ensures Unique:
    \forall integer y, z; 
      index <= y < index + size - 1 && index <= z < index + size - 1 && y != z ==> 
        array[y] != array[z];

  behavior empty:
    assumes size == 0;
    ensures \result == NULL;
    ensures *list == \old(*list);

  behavior one:
    assumes size == 1;
    ensures \result == array[index];
    ensures *list == NULL ; 
    ensures linked_n(*list, array, index, 0, NULL);
    
  behavior more:
    assumes size > 1;
    ensures \result == array[index+size-1];
    ensures array[index+size-2]->next == NULL;
    ensures linked_n(*list, array, index, size-1, NULL);
    ensures *list == \old(*list);
     
  disjoint behaviors;
  complete behaviors;
*/
void * list_chop(list_t list);

/*@
  requires \valid( list ) && \valid(item) ;
  requires \separated(list, item) ;
  requires Linked : linked_n (*list, array, index, n, NULL);
  requires ValidArray : \valid(array + (0 .. MAX_SIZE-1));
  requires 0 <= index < MAX_SIZE && 0 <= n < MAX_SIZE ;
  requires index+n < MAX_SIZE ;

  requires GhostSeparation: \separated(list, array + (0 .. MAX_SIZE - 1)) ;
  requires GhostSeparation: \separated(list, *(array + (index .. index + n - 1))) ;
  requires GhostSeparation: \separated(*list, array + (0 .. MAX_SIZE - 1)) ;

  requires \separated(item, array + (0 .. MAX_SIZE - 1)) ;
  requires Item_Separation:
    \forall integer i ; index <= i < index + n ==> 
      item != array[i] ==> \separated(item, array[i]);  

  requires Separation: 
    \forall integer y ; 
      index <= y < index + n ==> 
        \separated( * (array + y), array + (0 .. MAX_SIZE - 1));
  requires Separation : 
    \forall integer y, z; 
      index <= y < index + n && index <= z < index + n && z != y ==> 
        \separated( * (array + y), * (array + z) );
  requires Unique : 
    \forall integer y, z; 
      index <= y < index + n && index <= z < index + n && z != y ==> 
        array[z] != array[y] ;

  requires item_idx == index_of(item, array, index, index+n) ;

  assigns array[item_idx .. index+n-1], array[item_idx - 1]->next, *list,
          array[index + n - 1]->next, array[index + n - 2]->next,
	  array[index + n], array[index + n - 1],
	  item->next ;

  ensures GhostSeparation: \separated(list, array + (0 .. MAX_SIZE - 1)) ;
  ensures GhostSeparation: \separated(*list, array + (0 .. MAX_SIZE - 1)) ;

  behavior contains_item:
    assumes \exists integer i ; index <= i < index+n && array[i] == item ;
    ensures linked_n(*list, array, index, n, NULL);
    ensures unchanged{Pre,Post}(array, index, item_idx - 1);
    ensures array_swipe_left{Pre,Post}(array, item_idx, index + n - 1);
    ensures array[index+n-1] == item ;
    ensures item_idx > index ==> array[item_idx-1] == \old(array[item_idx-1]) ;

    ensures GhostSeparation: \separated(list, *(array + (index .. index + n - 1))) ;

    ensures Separation : 
      \forall integer y ; index <= y < index + n ==> 
          \separated( * (array + y), array + (0 .. MAX_SIZE - 1));

    ensures Separation : 
      \forall integer y, z; 
        index <= y < index + n && index <= z < index + n && z != y ==> 
          \separated( * (array + y), * (array + z) );

    ensures Unique:
      \forall integer y, z; 
        index <= y < index + n && index <= z < index + n && z != y ==> 
          array[z] != array[y] ;

  behavior does_not_contain_item:
    assumes \forall integer i ; index <= i < index+n ==> array[i] != item ;
    ensures linked_n(*list, array, index, n+1, NULL);
    ensures unchanged{Pre,Post}(array, index, index + n - 1);
    ensures End: n > 0 ==> array[index+n-1] == \old(array[index+n-1]);
    ensures array[index+n] == item ;

    ensures GhostSeparation: \separated(list, *(array + (index .. index + n))) ;

    ensures Separation : 
      \forall integer y ; index <= y < index + n + 1 ==> 
          \separated( * (array + y), array + (0 .. MAX_SIZE - 1));

    ensures Separation : 
      \forall integer y, z; 
        index <= y < index + n + 1 && index <= z < index + n + 1 && z != y ==> 
          \separated( * (array + y), * (array + z) );

    ensures Unique:
      \forall integer y, z; 
        index <= y < index + n + 1 && index <= z < index + n + 1 && z != y ==> 
          array[z] != array[y] ;

  complete behaviors ;
  disjoint behaviors ;
*/
void   list_add(list_t list, void *item);
/*@
  requires \valid( list ) && item != \null ;
  requires Linked : linked_n (*list, array, index, n, NULL);
  requires ValidArray : \valid(array + (0 .. MAX_SIZE-1));
  requires 0 <= index && 0 <= n < MAX_SIZE ;

  requires GhostSeparation: \separated(list, array + (0 .. MAX_SIZE - 1)) ;
  requires GhostSeparation: \separated(list, *(array + (index .. index + n - 1))) ;
  requires GhostSeparation: \separated(*list, array + (0 .. MAX_SIZE - 1)) ;
  
  requires Item_Separation:
    \forall integer i ; index <= i < index + n ==> 
      item != array[i] ==> \separated(item, array[i]);

  requires Separation : 
    \forall integer y ; 
      index <= y < index + n ==> 
        \separated( * (array + y), array + (0 .. MAX_SIZE - 1));

  requires Separation : 
    \forall integer y, z; 
      index <= y < index + n && index <= z < index + n && y != z ==> 
        \separated(* (array + y), * (array + z));

  requires Unique:
    \forall integer y, z; 
      index <= y < index + n && index <= z < index + n && y != z ==> 
        array[y] != array[z];

  requires item_idx == index_of(item, array, index, index+n) ;

  assigns array[item_idx .. index+n-1],
          array[item_idx - 1]->next,
	  *list ;

  ensures GhostSeparation: \separated(list, array + (0 .. MAX_SIZE - 1)) ;
  ensures GhostSeparation: \separated(*list, array + (0 .. MAX_SIZE - 1)) ;

  ensures UnchangedItem: *item == \old(*item);

  behavior contains_item:
    assumes \exists integer i ; (index <= i < index+n) && array[i] == item ;
    ensures Linked: linked_n(*list, array, index, n-1, NULL);
    ensures ItemNotIn: \forall integer x ; index <= x < index+n-1 ==> array[x] != item ;
    ensures IttemSep: \forall integer x ; index <= x < index+n-1 ==> \separated(item, array[x]) ;
    ensures GhostSeparation: \separated(list, *(array + (index .. index + n - 2))) ;
    ensures Separation : 
      \forall integer y ; 
        index <= y < index + n - 1 ==> 
          \separated( * (array + y), array + (0 .. MAX_SIZE - 1));
    ensures Separation : 
      \forall integer y, z; 
        index <= y < index + n - 1 && index <= z < index + n - 1 && y != z ==> 
          \separated(* (array + y), * (array + z));
    ensures Unique:
      \forall integer y, z; 
        index <= y < index + n - 1 && index <= z < index + n - 1 && y != z ==> 
          array[y] != array[z];
    ensures Unchanged: unchanged{Pre,Post}(array, index, item_idx - 1);
    ensures Swiped: array_swipe_left{Pre,Post}(array, item_idx, index + n - 1);
    ensures PrevItem: item_idx > index ==> array[item_idx - 1] == \old(array[item_idx - 1]);
    ensures UnchangedSwipe: 
      \forall integer i ; item_idx <= i < index + n - 1 ==>
        \at(*array[i], Post) == \at(*array[i+1], Pre);

  behavior does_not_contain_item:
    assumes \forall integer i ; index <= i < index+n ==> array[i] != item ;
    ensures linked_n(*list, array, index, n, NULL);
    ensures \forall integer x ; index <= x < index+n ==> array[x] != item ;
    ensures \forall integer x ; index <= x < index+n ==> \separated(item, array[x]) ;
    ensures GhostSeparation: \separated(list, *(array + (index .. index + n - 1))) ;
    ensures Separation : 
      \forall integer y ; 
        index <= y < index + n ==> 
          \separated( * (array + y), array + (0 .. MAX_SIZE - 1));
    ensures Separation : 
      \forall integer y, z; 
        index <= y < index + n && index <= z < index + n && y != z ==> 
          \separated(* (array + y), * (array + z));
    ensures Unique:
      \forall integer y, z; 
        index <= y < index + n && index <= z < index + n && y != z ==> 
          array[y] != array[z];
    ensures unchanged{Pre, Post}(array, index, index + n);

  complete behaviors;
  disjoint behaviors;
*/
void   list_remove(list_t list, void *item);

/*@
  requires \valid(list);
  requires linked_n(*list, array, index, n, NULL);
  
  assigns \nothing;

  ensures \result == n ;
*/
int    list_length(list_t list);

/*@
  requires ValidArray : \valid( array + (0 .. MAX_SIZE - 1) );
  requires \valid(src) && \valid(dest);
  requires linked_n(*src, array, index, n, NULL);
  requires \separated(dest, array + (0 .. MAX_SIZE - 1));
  requires \separated(dest, *(array + (index .. index + n - 1)));
  requires \separated(*dest, array + (0 .. MAX_SIZE - 1 ));
  assigns *dest;
  ensures linked_n(*dest, array, index, n, NULL);
  ensures linked_n(*src, array, index, n, NULL);
*/
void   list_copy(list_t dest, list_t src);

void   list_insert(list_t list, void *previtem, void *newitem);

/*@
  requires linked_n (item, array, index, n, NULL);
 
  assigns \nothing;

  behavior empty:
    assumes item == NULL ;
    ensures \result == NULL ;
    
  behavior not_empty:
    assumes item != NULL ;
    ensures linked_n (\result, array, index+1, n-1, NULL);
*/
void * list_item_next(void *item);

#endif /* LIST_H_ */

/** @} */
/** @} */
