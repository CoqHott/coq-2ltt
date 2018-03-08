From ModelStructure Require Import MLTT2.Overture.
From ModelStructure Require Import Reedy.Overture.
From ModelStructure Require Import Strict_eq.

Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.

(* String isomorphism *)

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
Defined.

(* Notation "[| x ≡ y :: p ; '___' ≡ z :: q ; '___' ≡ .. ; '___' ≡ u :: v |]" := *)
(*   (@Econcat _ x y z p (@Econcat _ y z z q .. (@Econcat _ _ _ _ v eq_refl) ..)) (at level 70). *)
(*   (cons    x (cons    y .. (cons    z nil    ) ..)) *)

Definition to_fn {A B : Type} (e : StrictIso A B) : A → B := @to A B e.
Infix "∙" := (to_fn) (at level 70).

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
    assert (Eap f (l x) ▹ˢ k (g (f x)) ≡ Etransport (λ x, F (f x)) (l x) (k (g (f x))))
      as step1 by apply Enaturality_transport.
    assert (Etransport (λ x, F (f x)) (l x) (k (g (f x))) ≡ k x) as step2 by apply (EapD k (l x)).
    apply (step1 E@ step2).
  - intros. apply functional_extensionality_dep. intros x'.
    apply EapD.
Defined.

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

(* Unset Printing Notations. *)

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
    (* Coq cannot infer the type family for transport and we have to provide it explicitly *)
    assert (Etransport (fun a : A => F (f a)) (l x₁)
                       (- (Eap f (l x₁)) ▹ˢ x₂) ≡
                       (Etransport (fun a : A => F (f a)) (l x₁) (-(l x₁) ▹ˢ x₂)))
      by apply (Enaturality_transport )


    (* (l x₁ ▹ ((r (f x₁))⁻¹ ▹ x₂)) *)
    (*         = (l x₁ ▹ (eq.symm (ap f (l x₁)) ▹ x₂)) : rfl *)
    (*     ... = (l x₁ ▹ (eq.symm (l x₁) ▹ x₂)) : naturality_subst *)
    (*     ... = ((l x₁ ⬝ (eq.symm (l x₁))) ▹ x₂) : transport_concat *)
    (*     ... = x₂ : concat_inv (l x₁) *)
    (*     end *)