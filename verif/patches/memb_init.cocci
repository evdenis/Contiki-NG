@memb_init@
identifier m;
@@
void
memb_init(struct memb *m)
{
-  memset(m->used, 0, m->num);
+  /*@
+    loop invariant valid_memb(m) && i <= m->num;
+    loop invariant \forall size_t j; j < i ==> m->used[j] == 0;
+    loop assigns i, m->used[0 .. m->num - 1];
+    loop variant m->num - i;
+  */
+  for(size_t i = 0; i < m->num; ++i){
+    m->used[i] = 0;
+  }
+  // memset(m->used, 0, m->num);
-  memset(m->mem, 0, m->size * m->num);
+  /*@
+    loop invariant valid_memb(m) && i <= m->num * m->size;
+    loop invariant \forall size_t j; j < i ==> ((char*)m->mem)[j] == 0;
+    loop assigns i, ((char*)m->mem)[0 .. m->size * m->num - 1];
+    loop variant m->num*m->size - i;
+  */
+  for(size_t i = 0; i < m->num * m->size; ++i) ((char*)m->mem)[i] = 0;
+  // memset(m->mem, 0, m->size * m->num);
}
