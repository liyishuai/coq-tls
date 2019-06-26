From Coq Require Import
     NArith
     String.
Open Scope N_scope.

(* https://tlswg.org/tls13-rfc/rfc8446.html#rfc.appendix.B.3.1 *)
Definition Version := N.
Definition TLS10 : Version := 769. (* 0x0301 *)
Definition TLS12 : Version := 771. (* 0x0303 *)
Definition TLS13 : Version := 772. (* 0x0304 *)

Definition ServerRandom  := string.
Definition ClientRandom  := string.

Definition SessionID     := string.
Definition Session       := option SessionID.
Definition CompressionID := N.

(* https://tlswg.org/tls13-rfc/rfc8446.html#rfc.appendix.B.4 *)
Definition CipherID  := N.
Definition TLS_AES_128_GCM_SHA256       : CipherID := 4865. (* 0x1301 *)
Definition TLS_AES_256_GCM_SHA384       : CipherID := 4866. (* 0x1302 *)
Definition TLS_CHACHA20_POLY1305_SHA256 : CipherID := 4867. (* 0x1303 *)
Definition TLS_AES_128_CCM_SHA256       : CipherID := 4868. (* 0x1304 *)
Definition TLS_AES_128_CCM_8_SHA256     : CipherID := 4869. (* 0x1305 *)

(* https://tlswg.org/tls13-rfc/rfc8446.html#rfc.section.4.2.7 *)
Definition Group := N.
Definition P256      : Group := 23.   (* 0x0017 *)
Definition P384      : Group := 24.   (* 0x0018 *)
Definition P521      : Group := 25.   (* 0x0019 *)
Definition x25519    : Group := 29.   (* 0x001D *)
Definition X448      : Group := 30.   (* 0x001E *)
Definition FFDHE2048 : Group := 256.  (* 0x0100 *)
Definition FFDHE3072 : Group := 257.  (* 0x0101 *)
Definition FFDHE4096 : Group := 258.  (* 0x0102 *)
Definition FFDHE6144 : Group := 259.  (* 0x0103 *)
Definition FFDHE8192 : Group := 260.  (* 0x0104 *)

Definition GroupPrivate := N.
Definition GroupPublic  := N.
Definition GroupKey     := N.

(* https://tlswg.org/tls13-rfc/rfc8446.html#rfc.section.4.4.4 *)
Definition FinishedData := string.
