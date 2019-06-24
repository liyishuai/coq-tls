From Coq Require Import
     List.
From ExtLib Require Import
     Extras
     Functor
     List
     Monad
     Traversable.
From ITree Require Import
     ITree.
From TLS Require Import
     Types
     Extensions
     Struct13.
Import
  FunctorNotation
  ListNotations
  MonadNotation.
Open Scope monad_scope.

Variant clientE : Type -> Set :=
  Client_Send            : Packet13 -> clientE unit
| Client_Recv            : clientE Packet13
| Client_Random          : clientE ClientRandom
| Client_GenerateKeyPair : Group -> clientE (GroupPrivate * GroupPublic).

Definition handshakeClient
           (cipher_suites    : list CipherID)
           (supported_groups : list Group) :
  itree clientE _ :=
  keyPairs <- forT supported_groups (embed Client_GenerateKeyPair);;
  let keyShareEntries : list KeyShareEntry :=
      uncurry Build_KeyShareEntry <$> zip supported_groups (snd <$> keyPairs) in
  let clientHelloExtensions : list Extension :=
      [Extension_SupportedVersions [TLS13];
       Extension_SupportedGroups supported_groups;
       Extension_KeyShare keyShareEntries] in
  clientRandom <- trigger Client_Random;;
  let client_hello : Handshake13 :=
      ClientHello13
        TLS12
        clientRandom
        None
        cipher_suites
        clientHelloExtensions in
  embed Client_Send (Packet_Handshake13 [client_hello]);;
  server_hello <- trigger Client_Recv;;
        (* TODO Server Hello    *)
        (* TODO Server Finished *)
        (* TODO Client Finished *)
  ret tt.
