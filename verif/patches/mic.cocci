@@
@@

static void mic(...) {
<...

-  memcpy(result, x, mic_len);
+  /*@
+    loop invariant 0 <= i <= mic_len;
+    loop assigns result[0 .. (mic_len - 1)], i;
+    loop variant mic_len - i;
+  */
+  for(i = 0; i < mic_len; i++)
+  {
+     result[i] = x[i];
+  }

...>
}
