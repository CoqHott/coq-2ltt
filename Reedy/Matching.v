From Categories Require Import Category.
From Categories Require Import Functor.
From Categories Require Import Ext_Cons.Comma.

From ModelStructure Require Import Reedy.Overture.
From ModelStructure Require Import MLTT2.Overture.


Import SubCategory.
Check CoSlice.

(* ref:def:reduced-coslice *)
(*  Definition 3.7 *)
(** We define the reduced coslice category as a full subcategory of non-identity arrows in Coslice  *)
Definition ReducedCoslice (C : Category) (z : C) : Category
  := Full_SubCategory (CoSlice C z)
                      (λ (x : Comma_Obj _ _),
                       Π (p : z ≡ CMO_trg x),
                       not (Etransport (λ y, y ⟶ CMO_trg x) p (CMO_hom x) ≡ id)).

Notation "z // C" := (ReducedCoslice C z) (at level 70).

(** We define a forgetful functor by projecting objects and arrows from the reduced coslice *)
Definition forget (C : Category) (c : C) : (c // C) ⇒ C :=
    {| FO := λ (a : c // C), CMO_trg (projT1 a);
       FA := λ (a b : c // C) (f : a ⟶ b), CMH_right (proj1_sig f);
       F_id := λ a, eq_refl _;
       F_compose := λ a b c f g, eq_refl _ |}.
