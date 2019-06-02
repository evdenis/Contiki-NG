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
identifier item, dest, src, list;
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
identifier list;
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

