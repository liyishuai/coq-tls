From Coq Require Import
     Basics
     NArith
     List.
From ExtLib Require Import
     Extras
     Functor
     List
     Monad
     Traversable.
From ITree Require Import
     Basics
     ITree.
From TLS Require Import
     Types
     Extensions
     Struct13.
Import
  FunctorNotation
  ListNotations
  Monads
  MonadNotation.
Open Scope monad_scope.
Open Scope program_scope.

Variant clientE : Type -> Set :=
  Client_Send            : Packet13 -> clientE unit
| Client_Recv            : clientE Packet13
| Client_Random          : clientE ClientRandom
| Client_GenerateKeyPair : Group -> clientE (GroupPrivate * GroupPublic).

Definition firstExpect {A} (f : A -> bool) : stateT (list A) option A :=
  fix firstExpect_rec (l : list A) :=
    match l with
    | [] => None
    | a :: l' => if f a then Some (l', a) else firstExpect_rec l'
    end.

Definition isServerHello13 (handshake13 : Handshake13) : bool :=
  match handshake13 with
  | ServerHello13 _ _ _ _ _ => true
  | _ => false
  end.

Definition isKeyShare (extension : Extension) : bool :=
  match extension with
  | Extension_KeyShare _ => true
  | _ => false
  end.

Definition calcSharedKey : Group -> GroupPublic -> GroupPrivate -> GroupKey :=
  (* TODO implement real groups, but not until prototype works. *)
  const N.mul.

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
  server_packet <- trigger Client_Recv;;
  match server_packet with
  | Packet_Handshake13 server_handshakes =>
    match firstExpect isServerHello13 server_handshakes with
    | Some (_, ServerHello13 TLS12 serverRandom None cipher_suite
                             serverHelloExtensions) =>
      match firstExpect isKeyShare serverHelloExtensions with
      | Some (_, Extension_KeyShare [server_share]) =>
        let group : Group := keyShareEntryGroup server_share in
        match find (N.eqb group ∘ keyShareEntryGroup) keyShareEntries with
        | Some client_share =>
          let handshakeSecret : GroupKey :=
              calcSharedKey group (keyShareEntryKeyExchange server_share)
                                  (keyShareEntryKeyExchange client_share) in
        (* TODO Server Finished *)
        (* TODO Client Finished *)
          ret (Some tt)
        | None => ret None
        end
      | _ => ret None
      end
    | _ => ret None
    end
  | Packet_AppData13 _ => ret None
  end.
