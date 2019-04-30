#ifndef LIST_LEMMAS_H
#define LIST_LEMMAS_H

/*@ lemma inverse:
  \forall struct list *root, **array, *bound, integer index, n ;
  linked_n(root, array, index, n, bound) ==>
  ( (0 <= index <= MAX_SIZE && n == 0 && bound == root) 
  || (  0 < n && 0 <= index 
  && 0 <= index + n <= MAX_SIZE
  && \valid(root)
  && root == array[index]
  && linked_n(root->next, array, index + 1, n - 1, bound) ) );
*/

/*@
  lemma transitive_unchanged{L1, L2, L3}:
    \forall struct list** array, integer down, up ;
      unchanged{L1, L2}(array, down, up) ==>
      unchanged{L2, L3}(array, down, up) ==>
      unchanged{L1, L3}(array, down, up) ;
*/
/* @
  lemma stay_linked{L1, L2}:
    \forall struct list *root, **array, *bound, integer i, n ;
      linked_n{L1} (root, array, i, n, bound) ==>
      unchanged{L1, L2}(array, i, i+n) ==>
        linked_n{L2} (root, array, i, n, bound);
*/
/* @ // Proved by Alt-ergo thanks to inverse
  lemma linked_n_starting_from_null_empty:
    \forall struct list **array, integer index, n ;
      linked_n(NULL, array, index, n, NULL) ==> n == 0;
*/
/* @ //==> function same name
  lemma linked_n_all_elements_not_null:
    \forall struct list *root, **array, *bound, integer i, n ;
      linked_n (root, array, i, n, bound) ==>
        (\forall integer j ; i <= j < i+n ==> array[j] != NULL) ;
*/
/* @ // ==> function linked_n_next_of_all_indexes
  lemma linked_last_next_index_bound :
    \forall struct list *root, **array, *bound, integer i, n ;
      n > 0 ==>
      linked_n (root, array, i, n, bound) ==> 
        array[i + n - 1]->next == bound;
*/
/* @ // ==> function same name
  lemma linked_n_bounds :
    \forall struct list *root, **array, *bound, integer i, n ;
      linked_n (root, array, i, n, bound) ==>
        ((n == 0 && 0 <= i <= MAX_SIZE) || (n > 0 && 0 <= i < MAX_SIZE));
*/
/* @ // ==> Proved by Alt-ergo thanks to inverse
  lemma linked_max_value_index_n:
    \forall struct list *root, **array, *bound, integer i, n ;
      linked_n (root, array, i, n, bound) ==> i + n - 1 < MAX_SIZE ;
*/
/* //==> function linked_n_valid_range
  lemma linked_valid_range :
    \forall struct list *root, **array, *bound, *node, integer i, n ;
      n > 0 ==>
      linked_n (root, array, i, n, bound) ==> 
        \valid(array[i .. i + n -1]);
*/
/* @ // ==> function linked_n_split_segment
  lemma linked_split_segment:
    \forall struct list *root, **array, *bound, *b0, integer i, n, k;
      n > 0 ==> k >= 0 ==>
        b0 == array[i + n - 1]->next ==>
        linked_n(root, array, i, n + k, bound) ==>
          (linked_n(root, array, i, n, b0) && linked_n(b0, array, i + n, k, bound));
*/
 
/* @ // ==> function linked_n_split_segment_direct
  lemma linked_split_segment_direct:
    \forall struct list *root, **array, *bound, *bound_split, 
      integer index, size, k;
      size > 0 ==> k > 0 ==>
      bound_split == array[index + size] ==>
      linked_n(root, array, index, size + k, bound) ==>
      ( linked_n(root, array, index, size, bound_split) && 
        linked_n(bound_split, array, index + size, k, bound) );
*/
/* @  //==> Proved by Alt-ergo thanks to inverse
  lemma linked_split_segment_left:
    \forall struct list *root, **array, *bound, integer i, n ;
      n > 0 ==>
      ((linked_n(root, array, i, n, bound) <==>             
      (linked_n(root, array, i, 1, root->next) &&
        linked_n(root->next, array, i+1, n-1, bound))));
*/
/* @ //==> function linked_n_split_segment_right
  lemma linked_split_segment_right:
    \forall struct list *root, **array, *bound, *b0, integer i, n ;
      n > 0 ==>
        b0 == array[i + n - 1]->next ==>
        linked_n(root, array, i, n + 1, bound) ==>
          (linked_n(root, array, i, n, b0) && linked_n(b0, array, i + n, 1, bound));
*/
/* @ //==> function linked_n_split_segment_right_riect
  lemma linked_split_segment_right_direct:
    \forall struct list *root, **array, *bound, *b0, integer i, n ;
      n > 0 ==>
        b0 == array[i + n] ==>
        linked_n(root, array, i, n + 1, bound) ==>
          (linked_n(root, array, i, n, b0) && linked_n(b0, array, i + n, 1, bound));
*/
/* @ // ==> function linked_n_merge_segment
  lemma linked_merge_segment:
    \forall struct list *root, **array, *bound, *b0, integer i, n, k;
      n >= 0 ==> k >= 0 ==>
      (linked_n(root, array, i, n, b0) && linked_n(b0, array, i + n, k, bound)) ==>
        linked_n(root, array, i, n + k, bound);
*/
/* @ //==> function linked_n_merge_segment_right
  lemma linked_merge_segment_right:
    \forall struct list *root, **array, *bound, *b0, integer i, n ;
      n >= 0 ==>       
      (linked_n(root, array, i, n, b0) && linked_n(b0, array, i + n, 1, bound)) ==>
        linked_n(root, array, i, n + 1, bound);
*/
/* @  //Proved by Alt-ergo thanks to inverse
  lemma linked_not_empty_head_position:
    \forall struct list *root, **array, *bound, integer i, n ;
      linked_n (root, array, i, n, bound) && n > 0 ==> root == array[i];
*/
/* @ // Proved by Alt-ergo thanks to inverse
  lemma linked_zero_root_equal_bound:
    \forall struct list *root, **array, *bound, integer i, n ;
      linked_n (root, array, i, n, bound) && n == 0 ==> root == bound;
*/
/* @  // Proved by Alt-ergo thanks to inverse
  lemma linked_root_not_bound_n_sup_zero:
    \forall struct list *root, **array, *bound, integer i, n ;
      linked_n (root, array, i, n, bound) && root != bound ==> n > 0;
*/
/* @
  lemma not_in_not_in_swipe_left{K, L}:
    \forall struct list **l, **array, integer index, n ;
      \separated(\at(l, K), \at(*(array + (index+1 .. index + n - 1)), K)) &&
      array_swipe_left{K, L} (array, index, index + n - 1) ==>
        \separated(\at(l, L), \at(*(array + (index .. index + n - 2)), L));
*/
/* @ // Proved by Alt-ergo thanks to inverse
  lemma linked_next_valid:
    \forall struct list *root, **array, *bound, integer i, n ;
      n > 1 ==>
      linked_n (root, array, i, n, bound) ==> 
        \valid(root->next);
*/
/* @ // Proved by Alt-ergo thanks to inverse
  lemma linked_next_index:
    \forall struct list *root, **array, *bound, integer i, n ;
      n > 1 ==>
      linked_n (root, array, i, n, bound) ==> 
        root->next == array[i + 1];
*/
/* @  ==> function
  lemma index_of_not_in_subrange:
    \forall struct list *item, **array, integer down, inter, up ;
      down >= 0 && up >= 0 && inter >= down ==>
      (\forall integer i ; down <= i < inter ==> array[i] != item) ==>
        index_of(item, array, down, up) ==
        index_of(item, array, inter, up) ;
*/
/* @  ==> function
  lemma index_of_unexisting_item:
    \forall struct list *item, **array, integer down, up ;
      down >= 0 && up >= 0 ==>
      (\forall integer i ; down <= i < up ==> array[i] != item) ==>
        index_of(item, array, down, up) == up ;
*/
/* @  ==> function
  lemma index_of_bounds:
    \forall struct list *item, **array, integer down, up ;
      0 <= down <= up ==>
      down <= index_of(item, array, down, up) <= up ;
*/
/* @  ==> function
  lemma index_of_existing_item:
    \forall struct list *item, **array, integer down, up ;
      down >= 0 && up >= 0 ==>
      (\exists integer i ; down <= i < up && array[i] == item) ==>
        down <= index_of(item, array, down, up) < up ;
*/

#endif /* LIST_LEMMAS_H */
