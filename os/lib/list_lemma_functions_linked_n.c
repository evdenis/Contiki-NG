#ifndef LIST_LEMMA_FUNCTIONS_LINKED_N_C
#define LIST_LEMMA_FUNCTIONS_LINKED_N_C

void linked_n_starting_from_null_empty(struct list **array, int index, int n)
{

}

void linked_n_all_elements_valid(struct list * root, struct list * bound,
                                 struct list **array, int index, int n)
{
  struct list* c = root;
  /*@
    loop invariant 0 <= i <= n ;
    loop invariant
      \forall integer j ; index <= j < index + i ==> \valid(array[j]);
    loop invariant linked_n(c, array, index+i, n - i, bound);
    loop assigns i, c;
    loop variant n - i ;
  */
  for(int i = 0; i < n ; ++i){
    c = c->next ;
  }
}

void linked_n_first_valid(struct list * root, struct list * bound,
                          struct list **array, int index, int n)
{

}

void linked_n_bounds(struct list * root, struct list * bound,
                     struct list **array, int index, int n)
{
  
}

void linked_n_valid_range(struct list* root, struct list* bound,
			  struct list** array, int index, int n) {
  struct list* c = root;
  /*@
    loop invariant 0 <= i <= n ;
    loop invariant
      \forall integer j ; index <= j < index + i ==> \valid(array[j]);
    loop invariant linked_n(c, array, index+i, n - i, bound);
    loop assigns i, c;
    loop variant n - i ;
  */
  for(int i = 0; i < n ; ++i){
    c = c->next ;
  }
}

void linked_n_next_of_all_indexes(struct list* root, struct list* bound,
                                  struct list** array, int index, int n){
  struct list* c = root;
  /*@
    loop invariant 0 <= i < n ;
    loop invariant
      \forall integer j ; index <= j < index + i ==> array[j]->next == array[j+1] ;
    loop invariant linked_n(c, array, index+i, n - i, bound);
    loop assigns i, c;
    loop variant n - i ;
  */
  for(int i = 0; i < n-1 ; ++i){
    c = c->next ;
  }
}

void linked_n_before_last(struct list* root, struct list* bound,
                          struct list** array, int index, int n){
  //@ ghost linked_n_valid_range(root, bound, array, index, n);
  //@ ghost linked_n_next_of_all_indexes(root, bound, array, index, n);
  /*@ assert \forall integer k ; index < k < index + n ==> 
        array[k - 1]->next == array[k] ;
  */

  
  struct list* c = array[index + n - 1] ;
  /*@
    loop invariant 0 <= i <= n-1 ;
    loop invariant linked_n(array[index + i], array, index+i, n-i-1, array[index + n - 1]) ;
    loop assigns i ;
  */
  for(int i = n - 1 ; i > 0 ; --i){
    //@ assert array[index + i - 1]->next == array[index + i] ;
  }
}

void linked_n_split_segment (struct list* root, struct list* bound, 
	                     struct list** array, int index, int n, struct list* b0, int k){
  //@ ghost linked_n_valid_range(root, bound, array, index, n+k);
  //@ ghost linked_n_next_of_all_indexes(root, bound, array, index, n+k);
  
  struct list* sep = array[index + n + k - 1] ;
  
  /*@
    loop invariant n <= i <= n + k ;
    loop invariant sep == array [ index + i - 1 ] ;
    loop invariant linked_n(root, array, index, i, sep->next) ;
    loop invariant linked_n(sep->next, array, index + i, (n + k) - i, bound) ;
    loop assigns i, sep ;
    loop variant i ;
  */
  for(int i = n + k ; i > n ; --i){
    //@ ghost linked_n_before_last(root, sep->next, array, index, i) ;
    //@ ghost linked_n_next_of_all_indexes(root, sep, array, index, i-1);
    //@ assert linked_n(root, array, index, i - 1, sep) ;
    
    //@ assert linked_n(sep->next, array, index + i, (n + k) - i, bound) ;
    //@ assert \valid(sep) ;
    //@ assert linked_n(sep, array, index + i - 1, (n + k)-(i-1), bound) ;
    
    sep = array[index + i - 2] ;
    //@ assert sep->next == array [ index + i - 1 ] ;
  }
}


void linked_n_split_segment_direct (struct list* root, struct list* bound,
				    struct list** array, int index, int n, struct list* b0, int k){
  //@ ghost linked_n_next_of_all_indexes(root, bound, array, index, n+k);
  //@ assert b0 == array[index + n - 1]->next ;
  //@ ghost linked_n_split_segment(root, bound, array, index, n, b0, k);
}

void linked_n_split_segment_right (struct list* root, struct list* bound, 
				   struct list** array, int index, struct list* b0, int n){
  //@ ghost linked_n_split_segment(root, bound, array, index, n, b0, 1);
}

void linked_n_split_segment_right_direct (struct list* root, struct list* bound, 
					  struct list** array, int index, struct list* b0, int n){
  //@ ghost linked_n_next_of_all_indexes(root, bound, array, index, n+1);
  //@ assert b0 == array[index + n - 1]->next ;
  //@ ghost linked_n_split_segment_right(root, bound, array, index, b0, n);
}

void linked_n_merge_segment(struct list *root, struct list* bound,
			    struct list**array, int index, int n, struct list *b0, int k){
  if (n == 0){
    //@ assert linked_n(root, array, index, n + k, bound) ;
  } else {
    //@ ghost linked_n_valid_range(root, b0, array, index, n);
    //@ ghost linked_n_next_of_all_indexes(root, b0, array, index, n);
    
    struct list* sep = array[index + n - 1] ;
    
    /*@
      loop invariant 1 <= i <= n ;
      loop invariant sep == array [ index + i - 1 ] ;
      loop invariant linked_n(root, array, index, i, sep->next) ;
      loop invariant linked_n(sep->next, array, index + i, k+(n-i), bound) ;
      loop assigns i, sep ;
      loop variant i ;
    */
    for(int i = n ; i > 1 ; --i){
      //@ ghost linked_n_before_last(root, sep->next, array, index, i) ;
      //@ ghost linked_n_next_of_all_indexes(root, sep, array, index, i-1);
      sep = array[index + i - 2] ;
    }
  }
}

void linked_n_merge_segment_right(struct list *root, struct list* bound, 
				  struct list**array, int index,  int n, struct list *b0){
  //@ ghost linked_n_merge_segment(root, bound, array, index, n, b0, 1);
}


void linked_n_all_elements(struct list* root, struct list* bound,
			   struct list** array, int index, int n){
  if(n > 0){
    struct list* c = root;
    /*@
      loop invariant index <= i <= index+n-1 ;
      loop invariant
        \forall integer j ; index <= j < i ==>
	  linked_n(array[j], array, j, n - (j - index), bound) ;
      loop invariant linked_n(c, array, i, n - (i - index), bound);
      loop assigns i, c;
      loop variant index + n - i ;
    */
    for(int i = index; i < index+n-1 ; ++i){
      c = c->next ;
    }
  }
}

#endif /* LIST_LEMMA_FUNCTIONS_LINKED_N_C */
