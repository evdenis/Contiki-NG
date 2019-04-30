#ifndef LIST_LOGIC_DEFS_H
#define LIST_LOGIC_DEFS_H

/*@
  inductive linked_n{L}(
    struct list *root, 
    struct list **array, 
    integer index, 
    integer n, 
    struct list *bound
  )
  {
    case linked_n_bound{L}:
      \forall struct list **array, *bound, integer index ;
	0 <= index <= MAX_SIZE ==>
	  linked_n(bound, array, index, 0, bound);
        
    case linked_n_cons{L}:
      \forall struct list *root, **array, *bound, integer index, n ;
        0 < n ==> 0 <= index ==> 
        0 <= index + n <= MAX_SIZE ==>
	\valid(root) ==> 
        root == array[index] ==>
	linked_n(root->next, array, index + 1, n - 1, bound) ==>
	  linked_n(root, array, index, n, bound);
  }
*/

/*@
  axiomatic Index_of_item {
    logic integer index_of(
      struct list *item, 
      struct list **array, 
      integer down, 
      integer up
    ) reads array[ down .. up-1 ];

  axiom no_more_elements:
    \forall struct list *item, **array, integer down, up ;
      0 <= up <= down ==> index_of(item, array, down, up) == up;
  
  axiom found_item:
    \forall struct list *item, **array, integer down, up ;
      0 <= down < up ==> array[down] == item ==> 
      index_of(item, array, down, up) == down;

  axiom not_the_item:
    \forall struct list *item, **array, integer down, up ;
       0 <= down < up ==> array[down] != item ==>
        index_of(item, array, down  , up) == 
	index_of(item, array, down+1, up) ;
  }
*/


/*@
  predicate unchanged{K,L}(struct list **array, integer down, integer up) =
    \forall integer i; down <= i < up ==>
      \at(array[i], K) == \at(array[i], L) &&     
      (\valid{K}(\at(array[i],K)) ==> \valid{L}(\at(array[i],L))) &&
      \at(*(array[i]), K) == \at(*(array[i]), L);
*/

/*@
  predicate array_swipe_left{K, L}(struct list **array, integer down, integer up) =
    \forall integer i; down <= i < up ==> \at(array[i], L) == \at(array[i+1], K);
*/
/*@
  predicate array_swipe_right{K, L}(struct list **array, integer down, integer up) =
    \forall integer i; down <= i < up  ==> \at(array[i], L) == \at(array[i-1], K);
*/

#endif /* LIST_LOGIC_DEFS_H */
