Set Warnings "-notation-overridden,-parsing".
Require Export ProofObjects.

Check nat_ind.

Theorem mult_0_r': forall n:nat,
  n * 0 = 0.
Proof.
  apply nat_ind.
  - reflexivity.
  - simpl. intros n' IHn'. rewrite -> IHn'.
  reflexivity.
  Qed.

Theorem plus_one_r': forall n:nat,
  n+1 = S n.
Proof.
  apply nat_ind.
  - reflexivity.
  - simpl. intros n' IHn'.
  rewrite -> IHn'. reflexivity.
  Qed.

Inductive yesno:Type :=
  | yes : yesno
  | no : yesno.

Check yesno_ind.

Inductive rgb : Type :=
  | red : rgb
  | green : rgb
  | blue : rgb.
Check rgb_ind.

Inductive natlist : Type :=
  | nnil : natlist
  | ncons : nat -> natlist -> natlist.
Check natlist_ind.

 Inductive natlist1 : Type :=
  | nnil1 : natlist1
  | nsnoc1 : natlist1 -> nat -> natlist1.

Check natlist1_ind.
