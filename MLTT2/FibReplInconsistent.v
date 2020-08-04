From TLTT Require Import MLTT2.Overture.


(* Introducing some notation *)

Notation "'reflˢ'" := (eq_refl) : path_scope.
Notation "'refl'" := (idpath) : path_scope.
Notation "'Π' x .. y , P" := (forall x, .. (forall y, P) ..) (at level 200, x binder, y binder, right associativity) : type_scope.

(* Definitions from MLTT2F *)
Module Export FibrantReplacement.

  Private Inductive repl (X: Type) : Type :=
  | η : X -> repl X.

  Arguments η {_} _.

  Axiom Fibrant_repl : forall (X : Type), Fibrant (repl X).

  Definition elimR {X} (P: repl X -> Type) {FibP : Π x, Fibrant (P x)}
             (H: Π x : X, P (η x))
    : Π z, P z.
  Proof.
    destruct z. apply H.
  Defined.
End FibrantReplacement.

Global Existing Instance Fibrant_repl.

Definition recR {X P} {FibP: Fibrant P} (H: X -> P)
  : repl X -> P
  := elimR (λ _ : repl X, P) H.


Theorem fibrant_replacement_inconsistent
        {A : Type} {FibA : Fibrant A} {x : A} (q : x = x) : q = refl.
Proof.
  assert (X : Π (a b : A) (p : a = b), repl (Π (h : a ≡ b), p = Eq_to_paths h)).
  { intros a b p.
    (* We can use induction on p, because repl (...) is fibrant *)
    destruct_path p.
    apply η. intros h.
    assert (Heq : h ≡ eq_refl) by apply Eq_UIP.
    rewrite Heq.
    exact refl. }

  (* We can get the goal by taking [h] to be [reflˢ] *)
  assert (f : (Π h : x ≡ x, q = Eq_to_paths h) -> q = refl) by exact (λ H, H reflˢ).

  (* We cannot apply [f] to [X x x q] directly, because the type is wrapped in [repl].
     We use the elimination principle for the fibrant relpacement to conclude the proof. *)
  apply (recR f (X _ _ q)).
Qed.