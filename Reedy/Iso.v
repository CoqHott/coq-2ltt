From ModelStructure Require Import MLTT2.Overture.
From ModelStructure Require Import Reedy.Overture.
From ModelStructure Require Import Strict_eq.

Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.

(* Strict isomorphism *)

Infix "∘" := (compose) (at level 70).

Class StrictIso (A B : Type) :=
  { to : A -> B;
    from : B -> A;
    left_inv : from ∘ to ≡≡ idmap;
    right_inv : to ∘ from ≡≡ idmap;
  }.


Notation "A ≃ˢ B" := (StrictIso A B) (at level 70).

Instance transitive_strict_iso {A B C : Type} (φ : A ≃ˢ B) (ψ : B ≃ˢ C) : A ≃ˢ C.
  destruct φ as [f g l r].
  destruct ψ as [f' g' l' r'].
  refine {| to:= f' ∘ f ;
            from := g ∘ g';
            left_inv := _;
            right_inv := _ |}.
- intros. rewrite l',l. reflexivity.
- intros. rewrite r,r'. reflexivity.
Qed.

(* Notation "[| x ≡ y :: p ; '___' ≡ z :: q ; '___' ≡ .. ; '___' ≡ u :: v |]" := *)
(*   (@Econcat _ x y z p (@Econcat _ y z z q .. (@Econcat _ _ _ _ v eq_refl) ..)) (at level 70). *)
(*   (cons    x (cons    y .. (cons    z nil    ) ..)) *)

Definition to_fn {A B : Type} (e : StrictIso A B) : A → B := @to A B e.
Infix "∙" := (to_fn) (at level 70).

Module StrictIso.
  Instance pi_congr₁ {A A' : Type} {F : A'  → Type} (φ : A ≃ˢ A')
    : (Π (a : A), F (φ ∙ a)) ≃ˢ (Π (a : A'), F a).
  Proof.
    destruct φ as [f g l r].
    simpl in *.
    (* Here I had to provide more type annotations in comparison with Lean code *)
    refine {| to:= (λ (k : Π (a : A), F (f a)) x', r x' ▹ˢ k (g x'));
              from := (λ (h : (Π (a : A'), F a)) x, h (f x));
              left_inv := _;
              right_inv := _ |}.
    - intros k. apply functional_extensionality_dep. intro x.
      assert (r (f x) ≡ Eap f (l x)) by apply Eq_UIP. rewrite H.
      rewrite Enaturality_transport.
      rewrite EapD.
      reflexivity.
    - intros. apply functional_extensionality_dep. intros x'.
      apply EapD.
  Qed.

  Instance pi_congr₂ {A : Type} {F G : A → Type} (φ : Π a, F a ≃ˢ G a)
    : (Π (a : A), F a) ≃ˢ (Π (a : A), G a).
  Proof.
    refine {| to:= λ x a, (φ a) ∙ x a;
              from := λ x b, from (x b);
              left_inv := _ ;
              right_inv := _ |}.
    - intros x. apply functional_extensionality_dep.
      intros a. rewrite left_inv. reflexivity.
    - intros x. apply functional_extensionality_dep.
      intros a. unfold to_fn. rewrite right_inv. reflexivity.
  Qed.

  Definition pi_congr {A A': Type} {F : A → Type} {F' : A' → Type}
             (φ : A ≃ˢ A') (φ' : Π a, F a ≃ˢ F' (φ ∙ a)) :  (Π a : A, F a) ≃ˢ (Π a : A', F' a)
    := _.

  Definition sigma_congr₁ {A B: Type} {F : B → Type} (φ : A ≃ˢ B):
    (Σ a : A, F (φ ∙ a)) ≃ˢ Σ b : B, F b.
    refine {| to:= λ (x : Σ a : A, F (φ ∙ a)), (φ ∙ x.1; x.2);
              from := λ x, (from x.1; Etransport (λ x, F x) (- right_inv x.1) x.2);
              left_inv := _;
              right_inv := _ |}.
    - intros.
      destruct φ as [f g l r].
      destruct x as [x₁ x₂]. simpl.
      unfold to_fn.
      apply (eq_sigma _ (l x₁)).
      replace (r (f x₁)) with (Eap f (l x₁)) by apply Eq_UIP.
      rewrite Eap_inv.
      rewrite Enaturality_transport.
      rewrite Etransport_concat.
      rewrite Econcat_inv_r.
      reflexivity.
    - intros x.
      destruct φ as [f g l r].
      destruct x as [x₁ x₂]. simpl.
      apply (eq_sigma _ (r x₁)).
      rewrite Etransport_concat.
      rewrite Econcat_inv_r.
      reflexivity.
  Qed.

  Definition sigma_swap {A B : Type} {F : A → B → Type} :
    (Σ (a : A) (b : B), F a b) ≃ˢ Σ (b : B) (a : A), F a b.
     refine {| to:= λ (x : Σ (a : A) (b : B), F a b), (x.2.1 ; (x.1; x.2.2));
               from := λ (x : Σ (b : B) (a : A), F a b), (x.2.1 ; (x.1; x.2.2));
               left_inv := _;
               right_inv := _ |}.
     - destruct x as [p1 p2]; destruct p2; reflexivity.
     - destruct x as [p1 p2]; destruct p2; reflexivity.
  Qed.

  Locate "↔".

  Instance iff_impl_equiv {A B : Prop} (Hiff : A ↔ B) : A ≃ˢ B.
  Proof.
    destruct Hiff as [f g].
    refine {| to := f;
       from := g;
       left_inv := λ x, proof_irrelevance _ _ _;
       right_inv := λ x, proof_irrelevance _ _ _ |}.
  Qed.

End StrictIso.
