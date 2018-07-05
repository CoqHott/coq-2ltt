From ModelStructure Require Import MLTT2.Overture.

(* sigT is redefined using primitive projections in ModelStructure.Overture.*)
Notation "'Σ' x .. y , P" := (sigT (fun x => .. (sigT (fun y => P)) ..)) (at level 200, x binder, y binder)  : type_scope.

Notation "x = y :> A" := (@paths A x y) : type_scope.
Notation "x = y" := (x = y :> _) : type_scope.

Definition singleton_contr {A : Type} {FibA : Fibrant A} (a : A)
      (s : Σ (b : A), a = b) : s = (a; idpath).
Proof.
  destruct s as [b p].
  destruct_path p. apply idpath.
Qed.


(** From [transport] and [singleton_contr] we can define [J]*)
Definition J (A : Type) {FibA : Fibrant A} (a : A)
           (C : forall b, a = b -> Type)
           {FibC : FibrantF2 C}
           (c : C a idpath) : forall (b : A) (p : a = b), C b p.
Proof.
  intros b p.
  pose (λ c, C c.1 c.2) as C'.
  assert (Heq : (a; idpath) = (b;p)) by (apply (inverse (singleton_contr _ _))).
  exact (transport C' Heq c).
Qed.


(** A bit longer way:
    we first pack a path [p] and a point [b] to a sigma-type to make
    the type family [C] not dependent. Then, we can definte a
    function [J' : C (a; idpath) -> forall c, C c] using the non-dependent
    eliminator [transport] and [singleton_contr].
    After that, we use [J'] to prove J *)

Definition J' (A : Type) {FibA : Fibrant A} (a : A)
           (C : (Σ b, a = b) -> Type)
           {FibC : FibrantF C}
           (c : C (a; idpath)) : forall c, C c.
Proof.
  intros c'.
  assert (Heq : (a; idpath) = c') by (apply (inverse (singleton_contr _ _))).
  exact (transport _ Heq c).
Qed.

Definition J_from_J' (A : Type) {FibA : Fibrant A} (a : A)
           (C : forall b, a = b -> Type)
           {FibC : FibrantF2 C}
           (c : C a idpath) : forall (b : A) (p : a = b), C b p.
Proof.
  intros b p.
  pose (λ c, C c.1 c.2) as C'.
  change (C' (b;p)).
  apply J';eauto.
Qed.
