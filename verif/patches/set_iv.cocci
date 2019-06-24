@@
@@

static void set_iv(...) {
<...

-  memcpy(iv + 1, nonce, CCM_STAR_NONCE_LENGTH);
+ /*@ 
+    loop invariant 0 <= i <= CCM_STAR_NONCE_LENGTH; 
+    loop assigns i, iv[1..13]; 
+    loop variant 13 - i; 
+  */
+  for(uint8_t i = 0; i < CCM_STAR_NONCE_LENGTH; i++)
+  {
+    iv[i+1] = nonce[i];
+  }

...>
}
