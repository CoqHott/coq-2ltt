(* -*- coq-prog-args: ("-top" "Reedy.Overture") -*-  *)

From Categories Require Import Category.
From Categories Require Import Functor.
From ModelStructure Require Import Reedy.Overture.

Require Import ModelStructure.MLTT2.Overture.

Require Import PeanoNat.
Require Import Coq.Logic.ProofIrrelevance.

Instance ℕop : Category :=
  {| Obj := nat;
     Hom := fun a b => ge a b;
     id := fun a => Nat.le_refl a;
     Category.compose := fun a b c p q =>
                  Nat.le_trans c b a q p;
     id_unit_left := fun (a b : nat) h
                     => proof_irrelevance _ _ _;
     id_unit_right:= fun (a b : nat) h
                     => proof_irrelevance _ _ _;
     assoc := fun a b c d g f h =>
                proof_irrelevance _ _ _;
     assoc_sym := fun a b c d g f h =>
                proof_irrelevance _ _ _;
  |}.

Definition hom_ℕop_id (x : ℕop) (f : x ⟶ x) : f ≡ id := @Eq_proof_irrel (x >= x) _ _.

(* ref:def:inverse-category *)
(*  Definition 3.8 *)
Section Invcat.
  Open Scope functor_scope.
  Open Scope object_scope.
  Open Scope morphism_scope.

  (* We have to explicitly provide a family in which transport
   happens, because in this particular case Coq cannot infer it. But
   if we inversed paths like [p: y ≡ x], the could used the notation
   for transport without the explicit type family argument. *)
  Definition id_reflect {C D: Category} (φ : C ⇒ D) :=
    Π {x y : C} (f : x ⟶ y),
    (Σ (q : φ _o x ≡ φ _o y), (Etransport (λ x, x ⟶ φ _o y) q (φ _a f)) ≡ id)
    → Σ (p : x ≡ y), (Etransport (λ x, x ⟶ y) p f) ≡ id.

 (* The definition of "refect identity" property specific to ℕop. *)
 (* Though it doesn't require for φ(f) to be the identity we will show, that *)
 (* id_reflect(C,ℕop) and id_reflect_ℕop(C) are logically equivalent *)
 Definition id_reflect_ℕop {C : Category} (φ : C ⇒ ℕop) :=
   Π {x y : C} (f : x ⟶ y),
   φ _o x ≡ φ _o y → Σ (p : x ≡ y), Etransport (λ x, x ⟶ y) p f ≡ id.

 Class ReflectsIds {C D : Category} (φ : C ⇒ D) :=
   reflecting_id : id_reflect φ.

 (* showing that id_reflect_ℕop φ ↔ id_reflect φ *)

 Definition IffT (A B : Type) := (A -> B) * (B -> A).
 Notation "A <--> B" := (IffT A B) (at level 70).

 Lemma id_reflect_ℕop_IffT {C : Category} {φ : C ⇒ ℕop} : id_reflect_ℕop φ <--> id_reflect φ.
 Proof.
   split.
   - intros id_r_ℕop x y f s.
     destruct s as [p q]. unfold id_reflect_ℕop in *. destruct (id_r_ℕop _ _ f p) as [p₁ p₂].
     apply (exist _ p₁). destruct p₁. simpl in *. exact p₂.
   - intros id_r x y f q.
     (* here we use the fact that any morphism x ⟶ x in ℕop only can be an identity morphism *)
     assert (f_is_id : Etransport (λ x, x ⟶ φ _o y) q (φ _a f) ≡ id)
       by apply (hom_ℕop_id _ _).
     destruct (id_r _ _ f (exist _ q f_is_id)) as [p₁ p₂].
     apply (exist _ p₁). destruct p₁. simpl in *. apply p₂.
 Qed.

 Class InvCat (C : Category) :=
   { φ_ic : C ⇒ ℕop;
     φ_reflects_id : ReflectsIds φ_ic }.
 
End Invcat.