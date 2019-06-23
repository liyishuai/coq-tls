From Coq Require Import
     NArith
     String.
From TLS Require Import
     Types
     Extensions.
Open Scope N_scope.

(* https://tlswg.org/tls13-rfc/rfc8446.html#rfc.appendix.B.3 *)
Variant Handshake13 :=
  ClientHello13
    (* https://tlswg.org/tls13-rfc/rfc8446.html#rfc.section.4.1.2 *)
    (legacy_version    : Version)
    (random            : ClientRandom)
    (legacy_session_id : Session)
    (cipher_suites     : list CipherID)
    (extensions        : list Extension)
| ServerHello13
    (* https://tlswg.org/tls13-rfc/rfc8446.html#rfc.section.4.1.3 *)
    (legacy_version    : Version)
    (random            : ServerRandom)
    (legacy_session_id : Session)
    (cipher_suite      : CipherID)
    (extensions        : list Extension)
| Finished13
    (* https://tlswg.org/tls13-rfc/rfc8446.html#rfc.section.4.4.4 *)
    (verify_data       : FinishedData).

Variant Packet13 :=
  Packet_Handshake13 : list Handshake13 -> Packet13
| Packet_AppData13   : string -> Packet13.
