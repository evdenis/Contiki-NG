/*@ requires linked_n(NULL, array, index, n, NULL);
  ensures (n == 0 );
  assigns \nothing ;
*/
void linked_n_starting_from_null_empty(struct list **array, int index, int n);

/*@ 
  requires ValidArray : \valid( array + (0 .. MAX_SIZE - 1) );
  requires linked_n (root, array, index, n, bound); 
  assigns \nothing ;
  ensures \forall int j ; index <= j < index+n ==> \valid(array[j]);
*/
void linked_n_all_elements_valid(struct list * root, struct list * bound,
                                 struct list **array, int index, int n);

/*@ requires linked_n(root, array, index, n, bound);
  @ requires n> 0;
  @ ensures \valid(root);
 */
void linked_n_first_valid(struct list * root, struct list * bound,
                          struct list **array, int index, int n);

/*@ 
  requires linked_n(root, array, index, n, bound);
  assigns \nothing ; 
  ensures ((n == 0 && 0 <= index <= MAX_SIZE) || 
           (n > 0 && 0 <= index < MAX_SIZE));
*/
void linked_n_bounds(struct list * root, struct list * bound,
                     struct list **array, int index, int n);

/*@
  requires Linked : linked_n (root, array, index, n, bound);
  requires ValidArray : \valid( array + (0 .. MAX_SIZE - 1) );
  requires 0 <= index ;

  assigns \nothing ;
  
  ensures \valid(array[index .. index + n - 1]) ;
*/
void linked_n_valid_range(struct list* root, struct list* bound,
			  struct list** array, int index, int n);

/*@   
  requires Linked : linked_n (root, array, index, n, bound);
  requires ValidArray : \valid( array + (0 .. MAX_SIZE - 1) );
  requires 0 <= index && 0 < n ;

  assigns \nothing ;
  
  ensures \forall integer k ; index < k < index + n ==> 
            array[k - 1]->next == array[k] ;
  ensures array[index+n-1]->next == bound ;
*/
void linked_n_next_of_all_indexes(struct list* root, struct list* bound,
                                  struct list** array, int index, int n);

/*@ 
  requires Linked : linked_n (root, array, index, n, bound);
  requires ValidArray : \valid( array + (0 .. MAX_SIZE - 1) );
  requires 0 <= index && 0 < n ;

  assigns \nothing ;

  ensures linked_n (root, array, index, n-1, array[index + n - 1]);
*/
void linked_n_before_last(struct list* root, struct list* bound,
                          struct list** array, int index, int n);

/*@
  requires Linked : linked_n (root, array, index, n + k, bound);
  requires ValidArray : \valid( array + (0 .. MAX_SIZE - 1) );
  requires 0 <= index ;
  requires 0 < n && k >= 0 ;
  requires b0 == array[index + n - 1]->next ;
  
  assigns \nothing ;

  ensures linked_n(root, array, index, n, b0) ;
  ensures linked_n(b0, array, index + n, k, bound);
*/
void linked_n_split_segment (struct list* root, struct list* bound, 
	                     struct list** array, int index, int n, struct list* b0, int k);

/*@
  requires Linked : linked_n (root, array, index, n + k, bound);
  requires ValidArray : \valid( array + (0 .. MAX_SIZE - 1) );
  requires 0 <= index ;
  requires 0 < n && k > 0 ;
  requires b0 == array[index + n] ;
  
  assigns \nothing ;

  ensures linked_n(root, array, index, n, b0) ;
  ensures linked_n(b0, array, index + n, k, bound);
*/
void linked_n_split_segment_direct (struct list* root, struct list* bound,
				    struct list** array, int index, int n, struct list* b0, int k);

/*@
  requires Linked : linked_n (root, array, index, n + 1, bound);
  requires ValidArray : \valid( array + (0 .. MAX_SIZE - 1) );
  requires n > 0 ;
  requires b0 == array[index + n - 1]->next ;
  
  assigns \nothing ;
  ensures linked_n(root, array, index, n, b0);
  ensures linked_n(b0, array, index + n, 1, bound);
*/
void linked_n_split_segment_right (struct list* root, struct list* bound, 
				   struct list** array, int index, struct list* b0, int n);

/*@
  requires Linked : linked_n (root, array, index, n + 1, bound);
  requires ValidArray : \valid( array + (0 .. MAX_SIZE - 1) );
  requires n > 0 ;
  requires b0 == array[index + n - 1]->next ;
  
  assigns \nothing ;
  ensures linked_n(root, array, index, n, b0);
  ensures linked_n(b0, array, index + n, 1, bound);
*/
void linked_n_split_segment_right_direct (struct list* root, struct list* bound, 
					  struct list** array, int index, struct list* b0, int n);

/*@ 
  requires Linked_1: linked_n(root, array, index, n, b0) ;
  requires Linked_2: linked_n(b0, array, index + n, k, bound) ;
  requires ValidArray : \valid( array + (0 .. MAX_SIZE - 1) );
  requires n >= 0 && k >= 0 ;
  
  assigns \nothing ;

  ensures linked_n(root, array, index, n + k, bound);
*/
void linked_n_merge_segment(struct list *root, struct list* bound,
			    struct list**array, int index, int n, struct list *b0, int k);

/*@ 
  requires Linked_1: linked_n(root, array, index, n, b0) ;
  requires Linked_2: linked_n(b0, array, index + n, 1, bound) ;
  requires ValidArray : \valid( array + (0 .. MAX_SIZE - 1) );
  requires n >= 0 ;
  
  assigns \nothing ;

  ensures linked_n(root, array, index, n + 1, bound);
*/
void linked_n_merge_segment_right(struct list *root, struct list* bound, 
				  struct list**array, int index,  int n, struct list *b0);

/*@
  requires Linked : linked_n (root, array, index, n, bound);
  requires ValidArray : \valid( array + (0 .. MAX_SIZE - 1) );
  requires 0 <= index ;

  assigns \nothing ;

  ensures \forall integer i ; index <= i < index+n ==>
    linked_n(array[i], array, i, n - (i - index), bound) ;
*/
void linked_n_all_elements(struct list* root, struct list* bound,
			   struct list** array, int index, int n);


/*
  Usage of stay_linked
    stay_linked(Label_1, Label_2, root, bound, array, index, n) ;

  The preprocessor will unfold it as a block containing a specified loop.
  To be proved, the invariant of the loop requires to use the function:
    linked_n_all_elements
  at the program point Label1. Basically, the scheme to use stay_linked
  is :

 L1:
  linked_n_all_elements(root, bound, array, index, n) ;

  //some operations

 L2:
  // Here we must be able to establish unchanged{L1,L2}(array, index, index+n) ;
  stay_linked(L1, L2, root, bound, array, index, n) ;
*/

#define stay_linked(L1, L2, __sl_rt, __sl_bnd, __sl_arr, __sl_idx, __sl_n) 	\
  /@ assert unchanged{L1,L2}(__sl_arr, __sl_idx, __sl_idx + __sl_n); @/		\
    if(__sl_n != 0){								\
      struct list* c = __sl_bnd ;						\
      /@									\
       loop invariant 0 <= __sl_i <= __sl_n ;					\
       loop invariant								\
       linked_n{L1}(c, __sl_arr, __sl_idx+__sl_i, __sl_n - __sl_i, __sl_bnd) ;	\
       loop invariant								\
       linked_n{L2}(c, __sl_arr, __sl_idx+__sl_i, __sl_n - __sl_i, __sl_bnd) ;	\
       loop assigns __sl_i, c;							\
       loop variant __sl_i ;							\
      @/									\
      for(int __sl_i = __sl_n ; __sl_i > 0 ; --__sl_i)				\
        c = __sl_arr[__sl_idx + __sl_i - 1] ;					\
      /@ assert linked_n{L2}(__sl_rt, __sl_arr, __sl_idx, __sl_n, __sl_bnd); @/	\
    } else {									\
      /@ assert linked_n{L2}(__sl_rt, __sl_arr, __sl_idx, 0, __sl_bnd); @/	\
    }										\
    /@ assert linked_n{L2}(__sl_rt, __sl_arr, __sl_idx, __sl_n, __sl_bnd); @/
