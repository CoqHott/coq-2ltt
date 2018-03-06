From Categories Require Import Category.
Require Import Functor.

Require Import ModelStructure.MLTT2.Overture.

Require Import PeanoNat.
Require Import Coq.Logic.ProofIrrelevance.

Notation "'λ' x .. y , t" := (fun x => .. (fun y => t) ..) (at level 200, x binder, y binder, right associativity).
Notation "'Π' x .. y , P" := (forall x, .. (forall y, P) ..) (at level 200, x binder, y binder, right associativity) : type_scope.
Notation "'Σ' x .. y , P" := (sigT (fun x => .. (sigT (fun y => P)) ..)) (at level 200, x binder, y binder)  : type_scope.
Notation "A ⇒ B" := (Functor A B) (at level 70).
Notation "a ⟶ b" := (Hom a b) (at level 90, b at level 200, right associativity).
Notation "x ≥ y" := (Nat.le y x)  (at level 70, no associativity).

(* Transport along strict equality *)
Notation "p ▹ˢ x" := (Etransport _ p x) (right associativity, at level 65).
(* Transport along fibrant equality *)
Notation "p ▹ x" := (transport _ p x) (right associativity, at level 65).

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

  Definition id_reflect {C D: Category} (φ : C ⇒ D) :=
    Π {x y : C} (f : x ⟶ y), (Σ q, (q ▹ˢ (φ _a f)) ≡ id)  → Σ p, (p ▹ˢ f) ≡ id.

 (* The definition of "refect identity" property specific to ℕop. *)
 (* Though it doesn't require for φ(f) to be the identity we will show, that *)
 (* id_reflect(C,ℕop) and id_reflect_ℕop(C) are logically equivalent *)
 Definition id_reflect_ℕop {C : Category} (φ : C ⇒ ℕop) :=
    Π {x y : C} (f : x ⟶ y), φ _o x ≡ φ _o y → (Σ p, p ▹ˢ f ≡ id).

 
(* ref:def:inverse-category *)
(*  Definition 3.8 *)
(* namespace invcat *)
(*   open sigma.ops iff *)
(*   definition id_reflect {C D: Category} (φ : C ⇒ D) := *)
(*     Π ⦃x y : C⦄ (f : x ⟶ y), (Σ (q : φ x = φ y), q ▹ φ f = id) → Σ (p : x = y),  p ▹ f = id *)

(*   Definition id_reflect' {C D: Category} := *)
(*   Π (φ : C ⇒ D) ⦃x y : C⦄ (f : x ⟶ y), (Σ (q : φ x = φ y), q ▹ φ f = id) → Σ (p : x = y),  p ▹ f = id *)

(*   -- definition if "refect identity" property specific to ℕop *)
(*   -- though it doesn't require for φ(f) to be the identity we will show, that *)
(*   -- id_reflect(C,ℕop) and id_reflect_ℕop(C) are logically equivalent *)
(*   definition id_reflect_ℕop {C : Category} (φ : C ⇒ ℕop) := *)
(*     Π ⦃x y : C⦄ (f : x ⟶ y), φ x = φ y → (Σ (p : x = y), p ▹ f = id) *)
