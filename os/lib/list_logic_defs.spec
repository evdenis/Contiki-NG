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
  predicate ptr_separated_from_range{L}
    (struct list* e, \list<struct list*> ll, integer beg, integer end) =
    \forall integer n ; 0 <= beg <= n < end <= \length(ll) ==> \separated(\nth(ll, n), e);

  predicate dptr_separated_from_range{L}
    (struct list** e, \list<struct list*> ll, integer beg, integer end) =
    \forall integer n ; 0 <= beg <= n < end <= \length(ll) ==> \separated(\nth(ll, n), e);

  predicate ptr_separated_from_list{L}(struct list* e, \list<struct list*> ll) =
    ptr_separated_from_range(e, ll, 0, \length(ll));
  predicate dptr_separated_from_list{L}(struct list** e, \list<struct list*> ll) =
    dptr_separated_from_range(e, ll, 0, \length(ll));
*/

/*@
  predicate in_list{L}(struct list* e, \list<struct list*> ll) =
    \exists integer n ; 0 <= n < \length(ll) && \nth(ll, n) == e ;
*/

/*@ 
  inductive linked_ll{L}(struct list *bl, struct list *el, \list<struct list*> ll) {
  case linked_ll_nil{L}:
    \forall struct list *el ; linked_ll{L}(el, el, \Nil);
  case linked_ll_cons{L}:
    \forall struct list *bl, *el, \list<struct list*> tail ;
      \separated(bl, el) ==> \valid(bl) ==>
      linked_ll{L}(bl->next, el, tail) ==>
      ptr_separated_from_list(bl, tail) ==>
        linked_ll{L}(bl, el, \Cons(bl, tail)) ;
  }
*/

/*@ 
  predicate all_separated_in_list(\list<struct list*> ll) =
    \forall integer n1, n2 ;
      0 <= n1 < \length(ll) ==>
      0 <= n2 < \length(ll) ==>
      n1 != n2 ==>
        \separated(\nth(ll, n1), \nth(ll, n2)) ;
*/

/*@ 
  predicate unchanged{L1, L2}(\list<struct list*> ll) =
    \forall integer n ; 0 <= n < \length(ll) ==>
      (\valid{L1}(\nth(ll,n))    && \valid{L2}(\nth(ll,n)) &&
      \at((\nth(ll,n))->next, L1) == \at((\nth(ll,n))->next, L2));
*/

/*@ 
  axiomatic To_ll {
    logic \list<struct list*> to_logic_list{L}(struct list* bl, struct list* el) 
      reads { e->next | struct list* e ; \valid(e) && in_list(e, to_logic_list(bl, el)) } ;
    
    axiom to_ll_nil{L}:
      \forall struct list *el ; to_logic_list{L}(el, el) == \Nil ;
      
    axiom to_ll_cons{L}:
      \forall struct list *bl, *el ;
        \separated(bl, el) ==>
        \valid(bl) ==>
	ptr_separated_from_list(bl, to_logic_list{L}(bl->next, el)) ==>
          to_logic_list{L}(bl, el) == (\Cons(bl, to_logic_list{L}(bl->next, el))) ;
  }
*/
