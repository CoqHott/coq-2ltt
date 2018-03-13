From Categories Require Import Category.
From Categories Require Import Functor.
From Categories Require Import Functor_Ops.
From Categories Require Import Ext_Cons.Comma.
From Categories Require Import Coq_Cats.Type_Cat.Type_Cat.
From Categories Require Import Coq_Cats.Type_Cat.Complete.
From Categories Require Import Limits.Limit GenProd_Eq_Limits.
From Categories Require Import Archetypal.Discr.Discr.
From Categories Require Import Ext_Cons.Arrow.


From ModelStructure Require Import Reedy.Inverse.
From ModelStructure Require Import MLTT2.Overture.
From ModelStructure Require Import Reedy.Overture.

From ModelStructure Require Import Strict_eq.

Require Import FunctionalExtensionality.

Import SubCategory.
Check CoSlice.

(* ref:def:reduced-coslice *)
(*  Definition 3.7 *)
(** We define the reduced coslice category as a full subcategory of
    non-identity arrows in Coslice. The coslice category is defined
    as an istance of more general comma category.*)
Definition ReducedCoslice (C : Category) (z : C) : Category
  := Full_SubCategory (CoSlice C z)
                      (λ (x : Comma_Obj _ _),
                       Π (p : z ≡ CMO_trg x),
                       not (Etransport (λ y, y ⟶ CMO_trg x) p (CMO_hom x) ≡ id)).

Notation "z // C" := (ReducedCoslice C z) (at level 70).

(* Projecting a "target" object, i.e. codomain of an arrow [z ⟶ c] *)
Definition rc_trg {C : Category} {z : C} (rc : z // C) : C := CMO_trg (projT1 rc).

(* Projecting the objects (which are the arrows [z ⟶ c] for some [c])
   of the reduced coslice category *)
Definition rc_obj {C : Category} {z : C} (rc : z // C)
  : z ⟶ rc_trg rc
  := CMO_hom (projT1 rc).

(** We define a forgetful functor by projecting objects and arrows from the reduced coslice *)
Definition forget (C : Category) (c : C) : (c // C) ⇒ C :=
    {| FO := λ (a : c // C), CMO_trg (projT1 a);
       FA := λ (a b : c // C) (f : a ⟶ b), CMH_right (proj1_sig f);
       F_id := λ a, eq_refl _;
       F_compose := λ a b c f g, eq_refl _ |}.
Notation "'Uˢ'" := Type_Cat.

Section MatchingObject.

  Import Limit.
  Import Const_Func.
  Import Arrow.

  Open Scope object_scope.
  Open Scope morphism_scope.
  Open Scope category_scope.

  Definition get_tip {C D : Category} {F : C ⇒ D} (L : Limit F) := cone_apex (LRKE L).

  (* We define the matching object to be a "tip" of the limit cone of the
     composition of functors [X ∘ (forget C z)].
     The limit is defined through the local right Kan extension. We apply projected cone tip
     to [tt : unit] to obtain a required pretype.
   *)
  Definition matching_object `{InvCat} (X : C ⇒ Uˢ) (z : C) : Uˢ
    := (get_tip (LimitOf (X ∘ (forget C z)))) _o tt.

  Lemma limit_cone_nat_transf_iff {C : Category} (X : C ⇒ Uˢ) (z : C) :
    (get_tip (LimitOf X) _o tt) <-> NatTrans (@Const_Func C Uˢ 1) X.
  Proof.
    split.
    - intros L. destruct L as [prod_cone eqls]. simpl in *.
      refine {| Trans := _; Trans_com := _; Trans_com_sym := _|}.
      unfold Projs, D_imgs in *. simpl in *.
      Unshelve. Focus 3.
      refine (λ c uu, prod_cone c).

      intros c c' h.
      apply functional_extensionality. intros x. simpl.
      apply (Ehapply_dep eqls (Build_Arrow _ _ _ h)).

      intros c c' h. apply functional_extensionality. intros x. simpl.
      apply (eq_sym (Ehapply_dep eqls (Build_Arrow _ _ _ h))).
    - intros NT. destruct NT as [η Nsq Nsq_sym].
      cbn in *.
      exists (λ c, η c tt).
      apply functional_extensionality_dep. intros f.
      destruct f. simpl.
      apply (Ehapply_dep (Nsq _ _ _) tt).
  Qed.

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
End MatchingObject.
