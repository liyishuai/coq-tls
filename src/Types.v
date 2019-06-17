From Coq Require Import
     NArith
     String.
Open Scope N_scope.

(* https://tlswg.org/tls13-rfc/rfc8446.html#rfc.appendix.B.3.1 *)
Definition Version := N.
Definition TLS10 : Version := 769. (* 0x0301 *)
Definition TLS12 : Version := 771. (* 0x0303 *)
Definition TLS13 : Version := 772. (* 0x0304 *)

Definition SessionID     := string.
Definition CompressionID := N.

(* https://tlswg.org/tls13-rfc/rfc8446.html#rfc.appendix.B.4 *)
Definition CipherID  := N.
Definition TLS_AES_128_GCM_SHA256       : CipherID := 4865. (* 0x1301 *)
Definition TLS_AES_256_GCM_SHA384       : CipherID := 4866. (* 0x1302 *)
Definition TLS_CHACHA20_POLY1305_SHA256 : CipherID := 4867. (* 0x1303 *)
Definition TLS_AES_128_CCM_SHA256       : CipherID := 4868. (* 0x1304 *)
Definition TLS_AES_128_CCM_8_SHA256     : CipherID := 4869. (* 0x1305 *)
