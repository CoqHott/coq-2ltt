From Categories Require Import Category.
From Categories Require Import Functor.
From Categories Require Import Functor_Ops.

From ModelStructure Require Import Reedy.Matching.
From ModelStructure Require Import Reedy.Fibration.
From ModelStructure Require Import Reedy.Inverse.
From ModelStructure Require Import MLTT2.Overture.
From ModelStructure Require Import Reedy.Overture.
Require Import FunctionalExtensionality.

Open Scope object_scope.
Open Scope morphism_scope.
Open Scope category_scope.

Definition matching_obj_map `{InvCat} (X : C ⇒ Uˢ) (z : C) :
    (X _o z) → matching_object X z.
Proof.
  intros x. cbn.
  exists (λ (a : z // C), X _a (rc_obj a) x).
  apply functional_extensionality_dep. intros f.
  destruct f as [s t f]. destruct f as [f cond]. simpl in *.
  destruct f as [uu hom comm_tr]. simpl in *. simpl_ids_in_I comm_tr.
  destruct t,s. unfold rc_obj. simpl in *. rewrite <- comm_tr.
  rewrite F_compose. reflexivity.
Defined.

Module Reedy.
  (* ref:def:reedy-fibration *)
  (* Definition 3.12 *)
  (* NOTE: our definition is less general then in the paper, since we do not define Reedy fibraion
     for any [Y], but instead take [Y=1] *)
  Definition reedy_fibrant {C : Category} {ic : InvCat C} (X : C ⇒ Uˢ) :=
    Π z, fibration_alt (matching_obj_map X z).
End Reedy.
