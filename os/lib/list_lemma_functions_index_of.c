
/*@ requires down >= 0 && up >= 0 && inter >= down;
  @ requires \forall int i ; down <= i < inter ==> array[i] != item;
  @ ensures index_of(item, array, down, up) == 
  @         index_of(item, array, inter, up);
  @ assigns \nothing;
  @*/
void index_of_not_in_subrange(struct list *item, struct list **array,
			      int down, int inter, int up)
{
  /*@ loop invariant down<= i <= inter;
    @ loop invariant i < inter ==> array[i] != item;
    @ loop invariant \forall int k; down <= k < i ==> 
    @                index_of(item, array, i, up) ==
    @                index_of(item, array, down, up);
    @ loop assigns i;
    @ loop variant inter - i;
    @ */
  for(int i = down; i < inter; i++);
}

/*@ requires down >= 0 && up >= 0;
  @ requires \forall int i ; down <= i < up ==> array[i] != item;
  @ ensures index_of(item, array, down, up) == up;
  @ assigns \nothing;
  @ */
void index_of_unexisting_item(struct list *item, struct list **array,
			      int down, int up)
{
  //@ ghost if (down<=up) index_of_not_in_subrange(item, array, down, up, up);
}

/*@ requires 0<= down <= up;
  @ requires index_of(item, array, down, up) == up;
  @ ensures \forall int i; down<= i< up ==> array[i] != item;
  @ assigns \nothing;
  @ */
void index_of_up_unexisting_item(struct list *item, struct list **array,
				 int down, int up)
{
  /*@ loop invariant down<= i <= up;
    @ loop invariant \forall int k; down<= k <  i ==> array[k] != item;
    @ loop invariant \forall int k; down <= k < i ==> 
    @                index_of(item, array, i, up) ==
    @                index_of(item, array, down, up);
    @ loop assigns i;
    @ loop variant up - i;
    @ */
  for(int i = down; i < up; i++);
}

/*@ requires 0<= down <= up;
  @ requires \valid(array+(down..up-1));
  @ requires down <= index_of(item, array, down, up) < up;
  @ ensures \exists integer i ; down <= i < up &&  array[i] == item ;
  @ assigns \nothing;
  @ */
void index_of_inter_existing_item(struct list *item, struct list **array,
				 int down, int up)
{ // TODO: simplify using index_of
  /*@ loop invariant down<= i <= up;
    @ loop invariant \forall int k; down<= k <  i ==> array[k] != item;
    @ loop invariant \forall int k; down <= k < i ==> 
    @                index_of(item, array, i, up) ==
    @                index_of(item, array, down, up);
    @ loop assigns i;
    @ loop variant up - i;
    @ */
  for(int i = down; i < up; i++)
    if(array[i] == item) break ;
}


/*@ requires down >= 0 && up >= 0;
  @ requires down<=up ==> \valid(array+(down..up-1));
  @ ensures \result == index_of(item, array, down, up);
  @ ensures down <= up ==> down <= \result <= up;@
  @ ensures \result < up ==> array[\result] == item;
  @ assigns \nothing;
  @ */
int index_of(struct list *item, struct list **array, int down, int up)
{
  if(up<=down) return up;
  int i = down;
  /*@ loop invariant down<= i <= up;
    @ loop invariant \forall int k; down<=k<i ==> array[k]!=item;
    @ loop assigns i;
    @ loop variant up - i;
    @ */
  while(i<up && array[i]!=item){
    i++;
  }
  //@ ghost index_of_not_in_subrange(item, array, down, i, up);
  return i;
}


/*@ requires 0 <= down <= up;
  @ requires \valid(array+(down..up-1));
  @ ensures down <= index_of(item, array, down, up) <= up;
  @ assigns \nothing;
  @ */
void index_of_bounds_weak(struct list *item, struct list **array,
			  int down, int up)
{
  //@ ghost int result = index_of(item,array,down,up);
}

/*@ requires down >= 0 && up >= 0;
  @ requires \valid(array+(down..up-1));
  @ requires \exists int i ; down <= i < up && array[i] == item;
  @ ensures down <= index_of(item, array, down, up) < up ;
  @ assigns \nothing;
  @ */
void index_of_existing_item_weak(struct list *item, struct list **array,
				 int down, int up)
{
  /*@ ghost 
    @ if (index_of(item, array, down, up) == up) 
    @ index_of_up_unexisting_item(item, array, down, up); */
}
