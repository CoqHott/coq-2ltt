From TLTT Require Import MLTT2.Overture.
From TLTT Require Import MLTT2.Path_eq.

Definition isProp (A : TypeF) := forall (a b : A), a = b.

Lemma hProp_is_Set {A : TypeF} (f : isProp A)
  : isSet A.
Proof.
  intros a b.
  intros p q. pose (fun (y : A) => f a y) as g.
  assert (H : forall (y z : A) (p : y = z), p = (g y)^ @ (g z)).
  { intros. apply moveL_Vp. rewi transport_paths_r; apply apD. }
  subst g. simpl in H. rew H.
Qed.
