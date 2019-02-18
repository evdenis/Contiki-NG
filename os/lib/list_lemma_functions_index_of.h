/*@ requires down >= 0 && up >= 0;
  @ requires down<=up ==> \valid(array+(down..up-1));
  @ ensures \result == index_of(item, array, down, up);
  @ ensures down <= up ==> down <= \result <= up;@
  @ ensures \result < up ==> array[\result] == item;
  @ assigns \nothing;
  @ */
int index_of(struct list *item, struct list **array, int down, int up);

/*@ requires down >= 0 && up >= 0 && inter >= down;
  @ requires \forall int i ; down <= i < inter ==> array[i] != item;
  @ ensures index_of(item, array, down, up) == 
  @         index_of(item, array, inter, up);
  @ assigns \nothing;
  @*/
void index_of_not_in_subrange(struct list *item, struct list **array,
			      int down, int inter, int up);

/*@ requires down >= 0 && up >= 0;
  @ requires \forall int i ; down <= i < up ==> array[i] != item;
  @ ensures index_of(item, array, down, up) == up;
  @ assigns \nothing;
  @ */
void index_of_unexisting_item(struct list *item, struct list **array,
			      int down, int up);

/*@ requires 0<= down <= up;
  @ requires index_of(item, array, down, up) == up;
  @ ensures \forall int i; down<= i< up ==> array[i] != item;
  @ assigns \nothing;
  @ */
void index_of_up_unexisting_item(struct list *item, struct list **array,
				 int down, int up);

/*@ requires 0<= down <= up;
  @ requires \valid(array+(down..up-1));
  @ requires down <= index_of(item, array, down, up) < up;
  @ ensures \exists integer i ; down <= i < up &&  array[i] == item ;
  @ assigns \nothing;
  @ */
void index_of_inter_existing_item(struct list *item, struct list **array,
				 int down, int up);

/*@ requires 0 <= down <= up;
  @ requires \valid(array+(down..up-1));
  @ ensures down <= index_of(item, array, down, up) <= up;
  @ assigns \nothing;
  @ */
void index_of_bounds_weak(struct list *item, struct list **array,
			  int down, int up);

/*@ requires down >= 0 && up >= 0;
  @ requires \valid(array+(down..up-1));
  @ requires \exists int i ; down <= i < up && array[i] == item;
  @ ensures down <= index_of(item, array, down, up) < up ;
  @ assigns \nothing;
  @ */
void index_of_existing_item_weak(struct list *item, struct list **array,
				 int down, int up);
