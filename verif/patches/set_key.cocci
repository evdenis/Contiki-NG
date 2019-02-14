@@
@@

static void set_key(...) {
<...

-  memcpy(round_keys[0], key, AES_128_KEY_LENGTH);
+ /*@  
+    loop invariant 0 <= i <= AES_128_KEY_LENGTH;
+    loop assigns i, round_keys[0][0 .. (AES_128_KEY_LENGTH - 1)];
+    loop variant AES_128_KEY_LENGTH - i;
+  */
+  for(i = 0; i < AES_128_KEY_LENGTH; i++) {
+    round_keys[0][i] = key[i];
+  }

...>
}
