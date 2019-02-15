#ifndef  __LOGIC_DEFS__MEMB__
#define  __LOGIC_DEFS__MEMB__ 1

/*
  Axiomatic and properties related to the occurence count of a specific
  element in an array.

  Modified to use arrays of char rather than arrays of int.

  Reference:
    Blanchard Allan, Nikolai Kosmatov, Matthieu Lemerre, Frédéric Loulergue. A
    case study on formal verification of the Anaxagoros hypervisor paging
    system with Frama-C. International Workshop on Formal Methods for
    Industrial Critical Systems (FMICS), Jun 2015, Oslo, Norway. Springer,
    2015, <http://fmics2015.org>. <hal-01140271>
    https://hal.inria.fr/hal-01140271
*/

/*@ axiomatic OccArray{
  @   logic integer occ_a{L}(integer e, char *t, 
  @                          integer from, integer to) 
  @                          reads t[from .. (to - 1)];
  @                          
  @ axiom end_occ_a{L}:
  @   \forall integer e, char *t, integer from, to; 
  @   from >= to ==> 
  @   occ_a{L}(e, t, from, to) == 0;
  @   
  @ axiom iter_occ_a_true{L}:
  @   \forall integer e, char *t, integer from, to; 
  @   (from < to && t[to-1] == e) ==> 
  @   occ_a{L}(e, t, from, to) == occ_a{L}(e, t, from, to-1) + 1;
  @   
  @ axiom iter_occ_a_false{L}:
  @   \forall integer e, char *t, integer from, to; 
  @   (from < to && t[to-1] != e) ==> 
  @   occ_a{L}(e, t, from, to) == occ_a{L}(e, t, from, to-1);
  @   }
  @   
  @*/

/*@ predicate not_in{L}(integer e, char *t, integer from, integer to) =
  @   \forall integer j; from <= j < to ==> t[j] != e;
  @   
  @*/

/*@ predicate everywhere{L}(integer e, char *t, integer from, integer to) =
  @   \forall integer j; from <= j < to ==> t[j] == e;
  @*/

/*@ // Validity of a MEMB.
  @ axiomatic MEMBValidity {
  @ 
  @ predicate valid_memb(struct memb *m) =
  @   \valid(m) && \valid(m->count) && \valid((char *)m->mem)  
  @   && \valid(m->count + (0 .. (m->num - 1)))
  @   && \valid((char*) m->mem + (0 .. (m->size * m->num - 1)))
  @   && m->size > 0
  @   && m->size * m->num <= INT_MAX
  @   && \separated(m->count + (0 .. (m->num - 1)), 
  @   (char*) m->mem + (0 .. m->size * m->num - 1));
  @
  @ // Converting from pointer to index and backwards.
  @ 
  @ logic integer _memb_index(struct memb *m, void *ptr) =
  @   (ptr - m->mem) / m->size;
  @   
  @ logic void *_memb_ptr(struct memb *m, integer index) =
  @   (void*) ((char*) m->mem + index * m->size);
  @
  @ // Not proved by SMTs !
  @  @ lemma mult_simplification:
  @   \forall integer a, b;
  @   a >= 0 ==> b > 0 ==> (a * b) / b == a;
  @
  @ }
  @ */


/*@ // Helper predicates. For readability.
  @ 
  @ predicate _memb_has(struct memb *m, void *ptr) =
  @   \exists integer i; 0 <= i < m->num && ptr == _memb_ptr(m, i);
  @   
  @ predicate _memb_allocated(struct memb *m, void *ptr) =
  @   _memb_has(m, ptr) && m->count[_memb_index(m, ptr)] != 0;
  @*/

/*@ // Couting free elements.
  @ 
  @ logic integer _memb_numfree(struct memb *m) = 
  @   occ_a(0, m->count, 0, m->num);
  @   
  @ predicate _memb_empty(struct memb *m) =
  @   \forall integer i; 0 <= i < m->num ==> m->count[i] == 0;
  @   
  @ predicate _memb_full(struct memb *m) =
  @   \forall integer i; 0 <= i < m->num ==> m->count[i] != 0;
  @   
  @*/

/*@ requires from <= cut <= to;
  @ ensures occ_a(e,t,from,to) == occ_a(e,t,from,cut)+occ_a(e,t,cut,to); 
  @ assigns \nothing;
  @ */
static inline void occ_a_split(int e, char * t, int from, int cut, int to)
{
  /*@ loop invariant cut<=i<=to;
    @ loop invariant occ_a(e,t,from,i) == occ_a(e,t,from,cut)+occ_a(e,t,cut,i);
    @ loop assigns i;
    @ loop variant to - i; 
    @*/
  for(int i = cut; i<to; i++);
}

#define same_elems_means_same_occ(_L1, _L2, _value, _array, _from, _to)	\
  /@									\
    loop invariant _from <= _k <= _to ;					\
    loop invariant occ_a{_L1}(_value, _array, _from, _k) ==		\
                   occ_a{_L2}(_value, _array, _from, _k) ; 		\
    loop assigns _k ;							\
    loop variant _to - _k ;						\
  @/									\
  for(int _k = _from ; _k < _to ; ++ _k) ;				\
  /@ assert occ_a{_L1}(_value, _array, _from, _to) ==			\
            occ_a{_L2}(_value, _array, _from, _to) ;			\
  @/

#endif /* __LOGIC__DEFS__MEMB__ */
