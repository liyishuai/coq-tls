From Coq Require Import
     NArith
     String.
From TLS Require Import Types.
Open Scope N_scope.

(* https://tlswg.org/tls13-rfc/rfc8446.html#rfc.appendix.B.3 *)
Definition HandshakeType := N.
Definition HandshakeType_ClientHello         : HandshakeType := 1.
Definition HandshakeType_ServerHello         : HandshakeType := 2.
Definition HandshakeType_NewSessionTicket    : HandshakeType := 4.
Definition HandshakeType_EndOfEarlyData      : HandshakeType := 5.
Definition HandshakeType_EncryptedExtensions : HandshakeType := 8.
Definition HandshakeType_Certificate         : HandshakeType := 11.
Definition HandshakeType_CertRequest         : HandshakeType := 13.
Definition HandshakeType_CertVerify          : HandshakeType := 15.
Definition HandshakeType_Finished            : HandshakeType := 20.
Definition HandshakeType_KeyUpdate           : HandshakeType := 24.
Definition HandshakeType_MessageHash         : HandshakeType := 254.

(* https://tlswg.org/tls13-rfc/rfc8446.html#rfc.appendix.B.3.1 *)
Definition ServerRandom := string.
Definition ClientRandom := string.
Definition Session      := option SessionID.

Definition ExtensionType := N.
Definition ExtensionType_ServerName                 : ExtensionType := 0.
Definition ExtensionType_MaxFragmentLength          : ExtensionType := 1.
Definition ExtensionType_StatusRequest              : ExtensionType := 5.
Definition ExtensionType_SupportedGroups            : ExtensionType := 10.
Definition ExtensionType_SignatureAlgorithms        : ExtensionType := 13.
Definition ExtensionType_UseSrtp                    : ExtensionType := 14.
Definition ExtensionType_Heartbeat                  : ExtensionType := 15.
Definition ExtensionType_ApplicationLayerProtocolNegotiation :
  ExtensionType := 16.
Definition ExtensionType_SignedCertificateTimestamp : ExtensionType := 18.
Definition ExtensionType_ClientCertificateType      : ExtensionType := 19.
Definition ExtensionType_ServerCertificateType      : ExtensionType := 20.
Definition ExtensionType_Padding                    : ExtensionType := 21.
Definition ExtensionType_PreSharedKey               : ExtensionType := 41.
Definition ExtensionType_EarlyData                  : ExtensionType := 42.
Definition ExtensionType_SupportedVersions          : ExtensionType := 43.
Definition ExtensionType_Cookie                     : ExtensionType := 44.
Definition ExtensionType_PskKeyExchangeModes        : ExtensionType := 45.
Definition ExtensionType_CertificateAuthorities     : ExtensionType := 47.
Definition ExtensionType_OidFilters                 : ExtensionType := 48.
Definition ExtensionType_PostHandshakeAuth          : ExtensionType := 49.
Definition ExtensionType_SignatureAlgorithmsCert    : ExtensionType := 50.
Definition ExtensionType_KeyShare                   : ExtensionType := 51.

Record Extension :=
  { extension_type : ExtensionType;
    extension_data : string }.

(* https://tlswg.org/tls13-rfc/rfc8446.html#rfc.appendix.B.3.1.3 *)
Definition SignatureScheme := N.
Definition SignatureScheme_RsaPkcs1Sha256       : SignatureScheme := 1025.
Definition SignatureScheme_RsaPkcs1Sha384       : SignatureScheme := 1281.
Definition SignatureScheme_RsaPkcs1Sha512       : SignatureScheme := 1537.
Definition SignatureScheme_EcdsaSecp256r1Sha256 : SignatureScheme := 1027.
Definition SignatureScheme_EcdsaSecp384r1Sha384 : SignatureScheme := 1283.
Definition SignatureScheme_EcdsaSecp521r1Sha512 : SignatureScheme := 1539.
Definition SignatureScheme_RsaPssRsaeSha256     : SignatureScheme := 2052.
Definition SignatureScheme_RsaPssRsaeSha384     : SignatureScheme := 2053.
Definition SignatureScheme_RsaPssRsaeSha512     : SignatureScheme := 2054.
Definition SignatureScheme_Ed25519              : SignatureScheme := 2055.
Definition SignatureScheme_Ed448                : SignatureScheme := 2056.
Definition SignatureScheme_RsaPssPssSha256      : SignatureScheme := 2057.
Definition SignatureScheme_RsaPssPssSha384      : SignatureScheme := 2058.
Definition SignatureScheme_RsaPssPssSha512      : SignatureScheme := 2059.
Definition SignatureScheme_RsaPkcs1Sha1         : SignatureScheme := 513.
Definition SignatureScheme_EcdsaSha1            : SignatureScheme := 515.

(* https://tlswg.org/tls13-rfc/rfc8446.html#rfc.appendix.B.3.3 *)
Definition CertificateType := N.
Definition CertificateType_X509         : CertificateType := 0.
Definition CertificateType_RawPublicKey : CertificateType := 2.

Variant SingleCertificate :=
  RawPublicKey (ASN1_subjectPublicKeyInfo : string)
| X509         (cert_data                 : string).

Record CertificateEntry :=
  { certificate : SingleCertificate;
    extensions  : list Extension }.

Record Certificate :=
  { certificate_request_context : string;
    certificate_list            : list CertificateEntry}.

Definition FinishedData := string.

(* https://tlswg.org/tls13-rfc/rfc8446.html#rfc.appendix.B.3.5 *)
Definition KeyUpdateRequest := N.
Definition KeyUpdateRequest_UpdateNotRequested : KeyUpdateRequest := 0.
Definition KeyUpdateRequest_UpdateRequested    : KeyUpdateRequest := 1.

Variant Handshake :=
  ClientHello
    (* https://tlswg.org/tls13-rfc/rfc8446.html#rfc.section.4.1.2 *)
    (legacy_version              : Version)
    (random                      : ClientRandom)
    (legacy_session_id           : Session)
    (cipher_suites               : list CipherID)
    (legacy_compression_methods  : list CompressionID)
    (extensions                  : list Extension)
| ServerHello
    (* https://tlswg.org/tls13-rfc/rfc8446.html#rfc.section.4.1.3 *)
    (legacy_version              : Version)
    (random                      : ServerRandom)
    (legacy_session_id           : Session)
    (cipher_suite                : CipherID)
    (legacy_compression_method   : CompressionID)
    (extensions                  : list Extension)
| CertRequest
    (* https://tlswg.org/tls13-rfc/rfc8446.html#rfc.section.4.3.2 *)
    (certificate_request_context : string)
    (extensions                  : list Extension)
| CertVerify
    (* https://tlswg.org/tls13-rfc/rfc8446.html#rfc.section.4.4.3 *)
    (algorithm                   : SignatureScheme)
    (signature                   : string)
| Finished
    (* https://tlswg.org/tls13-rfc/rfc8446.html#rfc.section.4.4.4 *)
    (verify_data                 : FinishedData)
| EndOfEarlyData
    (* https://tlswg.org/tls13-rfc/rfc8446.html#rfc.section.4.5 *)
| NewSessionTicket
    (* https://tlswg.org/tls13-rfc/rfc8446.html#rfc.section.4.6.1 *)
    (ticket_lifetime             : N)
    (ticket_age_add              : N)
    (ticket_nonce                : string)
    (ticket                      : string)
    (extensions                  : list Extension)
| KeyUpdate
    (* https://tlswg.org/tls13-rfc/rfc8446.html#rfc.section.4.6.3 *)
    (request_update              : KeyUpdateRequest).
