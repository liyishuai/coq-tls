From Coq Require Import
     NArith
     String.
From TLS Require Import Types.
Open Scope N_scope.

(* https://tlswg.org/tls13-rfc/rfc8446.html#rfc.section.4.2.8 *)
Record KeyShareEntry :=
  { keyShareEntryGroup       : Group;
    keyShareEntryKeyExchange : string }.

(* https://tlswg.org/tls13-rfc/rfc8446.html#rfc.section.4.2 *)
Variant Extension :=
  Extension_SupportedGroups     : list Group         -> Extension
| Extension_SupportedVersions   : list Version       -> Extension
| Extension_KeyShareClientHello : list KeyShareEntry -> Extension.
