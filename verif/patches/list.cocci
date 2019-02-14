@list_init@
identifier list;
typedef list_t;
@@

- void list_init(list_t list)
+ void list_init(list_t list, /* ghost: */ struct list **array)
{
  ...
}
