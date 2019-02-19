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

@list_add@
identifier list, item;
typedef list_t;
@@

- void list_add(list_t list, void *item)
+ void list_add(list_t list, struct list *item, /* ghost: */ struct list **array, int index, int n, int item_idx)
{
  ...
}

@list_chop@
identifier list;
typedef list_t;
@@

- struct list *list_chop(list_t list)
+ struct list *list_chop(list_t list, /* ghost: */ struct list **array, int index, int size)
{
  ...
}

@list_copy@
identifier dest, src;
typedef list_t;
@@

- void list_copy(list_t dest, list_t src)
+ void list_copy(list_t dest, list_t src, /* ghost: */ struct list **array, int index, int n)
{
  ...
}

@list_head@
identifier list;
typedef list_t;
@@

- struct list *list_head(list_t list)
+ struct list *list_head(list_t list, /* ghost: */ struct list **array, int index, int n)
{
  ...
}

@list_init@
identifier list;
typedef list_t;
@@

- void list_init(list_t list)
+ void list_init(list_t list, /* ghost: */ struct list **array)
{
  ...
}

@list_item_next@
identifier item;
@@

- struct list *list_item_next(void *item)
+ struct list *list_item_next(struct list *item, /* ghost: */ struct list **array, int index, int n)
{
  ...
}

@list_length@
identifier list;
typedef list_t;
@@

- int list_length(list_t list)
+ int list_length(list_t list, /* ghost: */ struct list **array, int index, int n)
{
  ...
}

@list_pop@
identifier list;
typedef list_t;
@@

- struct list *list_pop(list_t list)
+ struct list *list_pop(list_t list, /* ghost: */ struct list **array, int index, int n)
{
  ...
}

@list_push@
identifier list, item;
typedef list_t;
@@

- void list_push(list_t list, void *item)
+ void list_push(list_t list, struct list *item, /* ghost: */ struct list **array, int index, int n, int item_idx)
{
  ...
}

@list_remove@
identifier list, item;
typedef list_t;
@@

- void list_remove(list_t list, void *item)
+ void list_remove(list_t list, struct list *item, /* ghost: */ struct list **array, int index, int n, int item_idx)
{
  ...
}

@list_tail@
identifier list;
typedef list_t;
@@

- struct list * list_tail(list_t list)
+ struct list * list_tail(list_t list, /* ghost: */ struct list **array, int index, int n)
{
  ...
}

