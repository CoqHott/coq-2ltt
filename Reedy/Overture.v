(* -*- coq-prog-args: ("-top" "ModelStructure.Reedy.Overture") -*-  *)
From Categories Require Import Category.
From Categories Require Import Functor.
Require Import PeanoNat.
Require Import ModelStructure.MLTT2.Overture.

Notation "'λ' x .. y , t" := (fun x => .. (fun y => t) ..) (at level 200, x binder, y binder, right associativity).
Notation "'Π' x .. y , P" := (forall x, .. (forall y, P) ..) (at level 200, x binder, y binder, right associativity) : type_scope.

(* sigT is redefined using primitive projections in ModelStructure.Overture.*)
Notation "'Σ' x .. y , P" := (sigT (fun x => .. (sigT (fun y => P)) ..)) (at level 200, x binder, y binder)  : type_scope.
Notation "A ⇒ B" := (Functor A B) (at level 70).
Notation "a ⟶ b" := (Hom a b) (at level 90, b at level 200, right associativity).
Notation "x ≥ y" := (Nat.le y x)  (at level 70, no associativity).

(* Transport along strict equality *)
Notation "p ▹ˢ x" := (Etransport _ p x) (right associativity, at level 65).
(* Transport along fibrant equality *)
Notation "p ▹ x" := (transport _ p x) (right associativity, at level 65).

(* Inverse strict path *)
Notation "- p" := (Einverse p).