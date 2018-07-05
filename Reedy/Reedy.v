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