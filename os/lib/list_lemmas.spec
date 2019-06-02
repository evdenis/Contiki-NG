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

/*@
  lemma unchanged_sublists{L1, L2}:
    \forall \list<struct list*> l1, l2 ;
    unchanged{L1, L2}(l1 ^ l2) <==> (unchanged{L1, L2}(l1) && unchanged{L1, L2}(l2)) ;
*/

/*@
  lemma in_list_in_sublist:
    \forall struct list* e, \list<struct list*> rl, ll, l ;
    (rl ^ ll) == l ==>
    (in_list(e, l) <==> (in_list(e, rl) || in_list(e, ll))) ;
*/

/*@
  lemma ptr_separated_from_nil{L}:
    \forall struct list* l ; ptr_separated_from_list(l, \Nil);
  lemma ptr_separated_from_cons{L}:
    \forall struct list *e, *hd, \list<struct list*> l ; 
      ptr_separated_from_list(e, \Cons(hd, l)) <==>
      (\separated(hd, e) && ptr_separated_from_list(e, l));
  lemma ptr_separated_concat{L}:
    \forall struct list *e, \list<struct list*> l1, l2 ; 
      ptr_separated_from_list(e, l1 ^ l2) <==> 
        (ptr_separated_from_list(e, l1) && ptr_separated_from_list(e, l2)) ;

  lemma dptr_separated_from_nil{L}:
    \forall struct list** l ; dptr_separated_from_list(l, \Nil);
  lemma dptr_separated_from_cons{L}:
    \forall struct list **e, *hd, \list<struct list*> l ; 
      dptr_separated_from_list(e, \Cons(hd, l)) <==>
      (\separated(hd, e) && dptr_separated_from_list(e, l));
  lemma dptr_separated_concat{L}:
    \forall struct list **e, \list<struct list*> l1, l2 ; 
      dptr_separated_from_list(e, l1 ^ l2) <==> 
        (dptr_separated_from_list(e, l1) && dptr_separated_from_list(e, l2)) ;
*/

/*@ 
  lemma inversion_linked_ll{L}:
    \forall struct list *bl, *el, \list<struct list*> ll ;
      linked_ll(bl, el, ll) ==>
        ((bl == el && ll == \Nil)
        || 
        (\exists \list<struct list*> tl ;
         bl != el &&
         ll == \Cons(bl, tl) &&
         \valid(bl) && 
         \separated(bl, el) &&
         linked_ll{L}(bl->next, el, tl) &&
         ptr_separated_from_list(bl, tl))) ;
*/

/*@ 
  lemma separated_linked_ll_append{L}:
    \forall struct list *bl, *el, \list<struct list*> ll ;
      \valid(el) ==>
      linked_ll(bl, el, ll) ==>
      \separated(el, el->next) ==>
      ptr_separated_from_list(el->next, ll) ==>
        linked_ll(bl, el->next, ll ^ [| el |]) ;
*/

/*@ 
  lemma linked_ll_end{L}:
    \forall struct list *bl, *el, \list<struct list*> ll ;
      ll != \Nil ==> linked_ll(bl, el, ll) ==> 
        \nth(ll, \length(ll)-1)->next == el ;
*/

/*@ 
  lemma n_plus_1th_next{L}:
    \forall struct list *bl, *el, \list<struct list*> ll ;
      linked_ll(bl, el, ll) ==> 
        \forall integer n ; 0 <= n < \length(ll)-1 ==>
          \nth(ll, n)->next == \nth(ll, n+1) ;
*/

/*@ 
  lemma in_next_not_bound_in{L}:
    \forall struct list *bl, *el, *item, \list<struct list*> ll ;
      linked_ll(bl, el, ll) ==>
      in_list(item, ll) ==> item->next != el ==>
        in_list(item->next, ll);
*/

/*@ 
  lemma linked_ll_split{L}:
    \forall struct list *bl, *el, \list<struct list*> l1, l2;
      linked_ll(bl, el, l1 ^ l2) ==> l1 != \Nil ==>
        \let bound = \nth(l1, \length(l1) - 1)->next ;
        linked_ll(bl, bound, l1) && linked_ll(bound, el, l2) ;
*/

/*@ 
  lemma linked_ll_split_variant{L}:
    \forall struct list *bl, *bound, *el, \list<struct list*> l1, l2;
      linked_ll(bl, el, l1 ^ l2) ==> l1 != \Nil ==> l2 != \Nil ==>
      bound == \nth(l1 ^ l2, \length(l1 ^ l2) - \length(l2)) ==>
        linked_ll(bl, bound, l1) && linked_ll(bound, el, l2) ;
*/

/*@ 
  lemma all_separated_in_list_removed_element:
    \forall \list<struct list*> l1, l2, struct list* element ;
      all_separated_in_list(l1 ^  [| element |] ^ l2) ==>
        all_separated_in_list(l1 ^ l2);
*/
/*@ 
  lemma all_separated_in_list_added_element:
    \forall \list<struct list*> l1, l2, struct list* element ;
      all_separated_in_list(l1 ^ l2) && ptr_separated_from_list(element, l1 ^ l2) ==>
        all_separated_in_list(l1 ^ [| element |] ^ l2) ;
*/
/*@ 
  lemma linked_ll_merge{L}:
    \forall struct list *bl, *sl, *el, \list<struct list*> l1, l2;
      \separated(bl, el) ==>
      all_separated_in_list(l1 ^ l2) ==>
      ptr_separated_from_list(el, l1) ==>
      linked_ll(bl, sl, l1) && linked_ll(sl, el, l2) ==>
        linked_ll(bl, el, l1 ^ l2) ;
*/

/*@ 
  lemma linked_ll_unchanged{L1, L2}:
    \forall struct list *bl, *el, \list<struct list*> ll ;
      linked_ll{L1}(bl, el, ll) ==>
      unchanged{L1, L2}(ll) ==>
        linked_ll{L2}(bl, el, ll) ;
*/

/*@ 
  lemma linked_ll_unique_list{L}:
    \forall struct list *bl, *el, \list<struct list*> l1, l2 ;
      linked_ll(bl, el, l1) ==> linked_ll(bl, el, l2) ==> l1 == l2 ;
*/

/*@ 
  lemma linked_ll_in_valid{L}:
    \forall struct list *bl, *el, \list<struct list*> ll ;
      linked_ll(bl, el, ll) ==> 
        \forall integer n ; 0 <= n < \length(ll) ==> \valid(\nth(ll, n));
*/

/*@ 
  lemma linked_ll_in_valid_with_exists{L}:
    \forall struct list *bl, *el, \list<struct list*> ll ;
      linked_ll(bl, el, ll) ==> 
        \forall struct list* e ; in_list(e, ll) ==> \valid(e);
*/

/*@ 
  lemma linked_ll_all_separated{L}:
    \forall struct list *bl, *el, \list<struct list*> ll ;
      linked_ll(bl, el, ll) ==> all_separated_in_list(ll);
*/

/*@
  lemma linked_ll_in_beg_xor_end{L}:
    \forall struct list *bl, *el, *e, \list<struct list*> l1, l2 ;
      linked_ll(bl, el, l1 ^ l2) ==>
        (in_list(e, l1) ==> !in_list(e, l2)) &&
	(in_list(e, l2) ==> !in_list(e, l1)) ;
*/

/*@ 
  lemma linked_ll_end_not_in{L}:
    \forall struct list *bl, *el, \list<struct list*> ll ;
      linked_ll(bl, el, ll) ==> !in_list(el, ll);
*/

/*@ 
  lemma linked_ll_end_separated{L}:
    \forall struct list *bl, *el, \list<struct list*> ll ;
      linked_ll(bl, el, ll) ==> ptr_separated_from_list(el, ll);
*/

/*@ 
  lemma linked_ll_nth_separated_before_after{L}:
    \forall struct list *bl, *el, \list<struct list*> ll, integer n ;
      linked_ll(bl, el, ll) ==> 0 <= n < \length(ll) ==> (
        ptr_separated_from_range(\nth(ll, n), ll, 0, n) &&
        ptr_separated_from_range(\nth(ll, n), ll, n+1, \length(ll))
    );
*/

/*@ 
  lemma linked_ll_to_logic_list{L}:
    \forall struct list *bl, *el, \list<struct list*> ll ;
      linked_ll(bl, el, ll) ==> 
        ll == to_logic_list(bl, el);
*/

/*@ 
  lemma to_logic_list_unchanged{L1, L2}:
    \forall struct list *bl, *el, \list<struct list*> ll ;
      ll == to_logic_list{L1}(bl, el) ==>
      linked_ll{L1}(bl, el, ll) ==>
      unchanged{L1, L2}(ll) ==>
        ll == to_logic_list{L2}(bl, el) ;
*/

/*@ 
  lemma separated_to_logic_list_append{L}:
    \forall struct list *bl, *el, \list<struct list*> ll ;
      \valid(el) ==>
      to_logic_list(bl, el) == ll ==>
      linked_ll(bl, el, ll) ==>
      \separated(el, el->next) ==>
      ptr_separated_from_list(el->next, ll) ==>
        to_logic_list(bl, el->next) == (ll ^ [| el |]) ;
*/

/*@ 
  lemma to_logic_list_split{L}:
    \forall struct list *bl, *el, *sep, \list<struct list*> ll; 
      ll != \Nil ==> linked_ll(bl, el, ll) ==> ll == to_logic_list(bl, el) ==> 
        in_list(sep, ll) ==>
          ll == (to_logic_list(bl, sep) ^ to_logic_list(sep, el));
*/

/*@ 
  lemma to_logic_list_merge{L}:
    \forall struct list *bl, *sl, *el, \list<struct list*> l1, l2;
      \separated(bl, el) ==>
      linked_ll(bl, sl, l1) ==>
      all_separated_in_list(l1 ^ l2) ==>
      ptr_separated_from_list(el, l1) ==>
      to_logic_list(bl, sl) == l1 && to_logic_list(sl, el) == l2 ==>
        to_logic_list(bl, el) == (l1 ^ l2) ;
*/

/*@
  lemma linked_ll_in_points_to_same{L}:
    \forall struct list* bl, *el, *e1, *e2, \list<struct list*> ll ;
      linked_ll(bl, el, ll) ==>
      in_list(e1, ll) ==> in_list(e2, ll) ==> e1->next == e2->next ==> e1 == e2 ;
*/
