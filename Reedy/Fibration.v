(* -*- coq-prog-args: ("-top" "Reedy") -*-  *)
From ModelStructure Require Import MLTT2.Overture.
From ModelStructure Require Import Reedy.Overture.
From ModelStructure Require Import Reedy.Iso.

(* Strict fibre *)
Definition fibre_s {X Y : Type} (f : X → Y) (y : Y) := Σ (x : X), f x ≡ y.

(* NOTE: cannot make superscript s part of the definition, because of the lexer limitations*)
Notation "'fibreˢ'" := fibre_s.

Lemma fibre_projection {X : Type}{Y : X → Type}(x : X)
  : (fibreˢ (λ (p : Σ (x : X), Y x), p.1) x) ≃ˢ (Y x).
Proof.
  unfold fibre_s.
  pose (λ (a: (Σ (a : Σ b : X, Y b), a.1 ≡ x)), a.2 ▹ˢ a.1.2) as f.
  (* NOTE: next statement builds a term wrong type *)
  pose (λ (a : Y x), ((x; a); @eq_refl _ _)) as _g.
  (* To get correct type we have to provide the type family explicitly *)
  pose (λ (a : Y x), (exist (λ y, y.1 ≡ x) (exist _ x a) eq_refl)) as g.
  refine (Build_StrictIso _ _ f g _ _).
  - intros a. destruct a as [a₁ a₂]. destruct a₂.  reflexivity.
  - apply (λ (y : Y x), refl).
Qed.

(* ref:def:fibration *)
(* Definition 3.2 *)
Definition fibration {E B : Type} (p : E → B) : Type :=
  Σ (F : B → TypeF), Π (b : B), F b ≃ˢ (fibreˢ p b).

Definition fibration_alt {E B : Type} (p : E → B) :=
  Π (b : B), Fibrant (fibreˢ p b).
