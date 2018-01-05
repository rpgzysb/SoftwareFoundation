Require Export MBasics.

Theorem plus_n_0_firsttry : forall n : nat,
  n = n + 0.
Proof.
  intros n.
  simpl.
  Abort.

Theorem plus_n_0_secondtry : forall n : nat,
  n = n + 0.
Proof.
  intros n. 
  destruct n as [| n'].
  - reflexivity.
  - simpl.
  Abort.

Theorem plus_n_0 : forall n : nat, 
  n = n + 0.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl.
  rewrite <- IHn'.
  reflexivity.
  Qed.

Theorem minus_diag : forall n,
  minus n n = 0.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl.
  rewrite -> IHn'.
  reflexivity.
  Qed.

(* Exercise basic induction *)
Theorem mult_0_r : forall n : nat,
  n * 0 = 0.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl.
  rewrite -> IHn'.
  reflexivity.
  Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof. 
  intros n m.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl.
  rewrite -> IHn'.
  reflexivity.
  Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - simpl.
  rewrite <- plus_n_0.
  reflexivity.
  - simpl.
  rewrite -> IHn'.
  rewrite -> plus_n_Sm.
  reflexivity.
  Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl.
  rewrite <- IHn'.
  reflexivity.
  Qed.

(* Exercise double plus *)
Fixpoint double (n:nat) := 
  match n with 
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n : nat,
  double n = n + n.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl.
  rewrite -> IHn'.
  rewrite <- plus_n_Sm.
  reflexivity.
  Qed.

(* Exercise evenb S *)
Theorem evenb_S : forall n : nat,
  evenb (S n) = negb (evenb n).
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - rewrite -> IHn'.
  rewrite -> negb_involutive.
  reflexivity.
  Qed.

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). { reflexivity. }
  rewrite -> H.
  reflexivity.
  Qed.

Theorem plus_rearrange : 
  forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite -> plus_comm. reflexivity. }
  rewrite -> H.
  reflexivity.
  Qed.

Theorem beq_nat_refl: forall n1:nat,
  beq_nat n1 n1 = true.
Proof.
  intros n1.
  induction n1 as [|n' IHn'].
  - reflexivity.
  - simpl. apply IHn'.
  Qed. 

