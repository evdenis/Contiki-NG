@@
identifier next;
@@

struct list {
  struct list *next;
+ int k;
};

@@
@@

typedef
- void **
+ struct list **
list_t;

@list_decl@
identifier previtem, newitem, item, list;
typedef list_t;
@@

(
- void list_add(list_t list, void *item)
+ void list_add(list_t list, struct list *item)
;
|
- void *list_item_next(void *item)
+ struct list *list_item_next(struct list *item)
;
|
- void list_push(list_t list, void *item)
+ void list_push(list_t list, struct list *item)
;
|
- void list_remove(list_t list, void *item)
+ void list_remove(list_t list, struct list *item)
;
|
- void * list_tail(list_t list)
+ struct list * list_tail(list_t list)
;
|
- void *list_chop(list_t list)
+ struct list *list_chop(list_t list)
;
|
- void list_insert(list_t list, void *previtem, void *newitem)
+ void list_insert(list_t list, struct list *previtem, struct list *newitem)
;
)

@list_add@
identifier list, item;
typedef list_t;
@@

- void list_add(list_t list, void *item)
+ void list_add(list_t list, struct list *item)
{
  ...
}

@list_item_next@
identifier item;
@@

- void *list_item_next(void *item)
+ struct list *list_item_next(struct list *item)
{
  ...
}

@list_push@
identifier list, item;
typedef list_t;
@@

- void list_push(list_t list, void *item)
+ void list_push(list_t list, struct list *item)
{
  ...
}

@list_remove@
identifier list, item;
typedef list_t;
@@

- void list_remove(list_t list, void *item)
+ void list_remove(list_t list, struct list *item)
{
  ...
}

@list_tail@
identifier list, l;
typedef list_t;
@@

- void * list_tail(list_t list)
+ struct list * list_tail(list_t list)
{
+ int n;
  ...
- for(l = *list; l->next != NULL; l = l->next);
+ for(l = *list; l->next != NULL; l = l->next) {
+    //@ assert \valid(l);
+    //@ assert 0 <= n < \length(to_logic_list(*list, NULL))-1 ;
+    ++n;
+ }
  ...
}

@list_chop@
identifier list, l;
typedef list_t;
@@

- void *list_chop(list_t list)
+ struct list *list_chop(list_t list)
{
+  int n;
  ...
  if(((struct list *)*list)->next == NULL) {
    ...
  }
+  l = *list;
  ...
-  for(l = *list; l->next->next != NULL; l = l->next);
+  while(l->next->next != NULL){
+    //@ assert in_list(l->next, to_logic_list(*list, NULL)) ;
+    //@ assert all_separated_in_list(to_logic_list(*list, NULL)) ;
+    //@ assert in_list(l, to_logic_list(*list, NULL)) ;
+    //@ assert to_logic_list(*list, NULL) == (to_logic_list(*list, l) ^ to_logic_list(l, NULL)) ;
+    /*@ assert \forall integer i ; 0 <= i < \length(to_logic_list(*list, l)) ==>
+        \separated(\nth(to_logic_list(*list, NULL), i),
+	           \nth(to_logic_list(*list, NULL), \length(to_logic_list(*list, l))+1)) ;
+    */
+    //@ assert \nth(to_logic_list(*list, NULL), \length(to_logic_list(*list, l))+1) == l->next ;
+    /*@ assert \forall integer i ; 0 <= i < \length(to_logic_list(*list, l)) ==>
+        \nth(to_logic_list(*list, NULL), i) == \nth(to_logic_list(*list, l), i) ;
+    */
+    //@ assert ptr_separated_from_list(l->next, to_logic_list(*list, l)) ;
+    //@ assert to_logic_list(*list, l->next) == (to_logic_list(*list, l) ^ [| l |]) ;  
+    l = l->next ;
+    ++n ;
+  }
  ...
}

@list_insert@
identifier list, previtem, newitem;
typedef list_t;
@@
- void list_insert(list_t list, void *previtem, void *newitem)
+ void list_insert(list_t list, struct list *previtem, struct list *newitem)
{
  ...
}
