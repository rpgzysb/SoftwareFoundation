Set Warnings "-notation-overridden,-parsing".
Require Export Poly.

Theorem silly1 : forall (n m o p : nat),
  n = m ->
  [n;o] = [n;p] ->
  [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.
  apply eq2.
  Qed.

Theorem silly2: forall (n m o p : nat),
  n = m ->
  (forall (q r : nat), q = r -> [q;o] = [r;p]) ->
  [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2.
  apply eq1.
  Qed.

Theorem silly2a: forall (n m : nat),
  (n,n) = (m,m) ->
  (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) -> 
  [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1. Qed.

(* Exercise silly_ex *)
Theorem silly_ex : 
  (forall n, evenb n = true -> oddb (S n) = true) ->
  evenb 3 = true -> 
  oddb 4 = true.
Proof.
  intros eq1 eq2.
  apply eq1. apply eq2.
  Qed.

Theorem silly3_firsttry : forall (n : nat),
  true = beq_nat n 5 ->
  beq_nat (S (S n)) 7 = true.
Proof.
  intros n H.
  simpl.
  symmetry.
  apply H.
  Qed.

(* Exercise apply_exercise1 *)
Theorem rev_exercise1: forall (l l' : list nat),
  l = rev l' ->
  l' = rev l.
Proof.
  intros l l'. intros H.
  symmetry.
  rewrite -> H.
  Search rev.
  apply rev_involutive.
  Qed.

Example trans_eq_example : forall (a b c d e f : nat),
  [a;b] = [c;d] -> 
  [c;d] = [e;f] ->
  [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1.
  rewrite -> eq2.
  reflexivity. Qed.

Theorem trans_eq : forall (X : Type)(n m o: X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2.
  rewrite -> eq1. rewrite -> eq2. reflexivity.
  Qed.

Example trans_eq_example' : forall (a b c d e f : nat),
  [a;b] = [c;d] -> 
  [c;d] = [e;f] ->
  [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (m:=[c;d]).
  apply eq1. apply eq2. Qed.

(* Exercise apply_with_exercise *)
Example trans_eq_exercise: forall (n m o p : nat),
  m = (minustwo o) ->
  (n + p) = m ->
  (n + p) = (minustwo o).
Proof.
  intros n m o p eq1 eq2.
  apply trans_eq with (m:=m).
  apply eq2.
  apply eq1.
  Qed.

Theorem S_injective : forall (n m : nat), 
  S n = S m -> n = m.
Proof.
  intros n m H.
  inversion H.
  reflexivity.
  Qed.

Theorem inversion_ex1 : forall (n m o : nat),
  [n;m] = [o;o] -> 
  [n] = [m].
Proof.
  intros n m o H. inversion H as [Hnm].
  reflexivity. Qed.

Example inversion_ex3 : forall (X : Type)
  (x y z : X)(l j : list X),
  x::y::l = z::j ->
  y::l = x::j ->
  x = y.
Proof.
  intros X x y z l j.
  intros eq1 eq2.
  inversion eq2.
  reflexivity.
  Qed.

Theorem beq_nat_0_l : forall n,
  beq_nat 0 n = true -> n = 0.
Proof.
  intros n.
  destruct n as [| n'].
  - intros H. reflexivity.
  - simpl. intros H.
  inversion H.
  Qed.

Theorem inversion_ex4 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra. inversion contra. Qed.

Theorem inversion_ex5 : forall (n m : nat),
  false = true ->
  [n] = [m].
Proof.
  intros n m contra. inversion contra. Qed.

Example inversion_ex6 : forall (X:Type)
  (x y z : X)(l j : list X),
  x::y::l = [] -> 
  y::l = z::j ->
  x = z.
Proof.
  intros X x y z l j eq1 eq2.
  inversion eq1.
  Qed.

Theorem f_equal : forall (A B : Type)(f:A->B)
  (x y : A),
  x = y -> f x = f y.
Proof.
  intros A B f x y eq.
  rewrite eq.
  reflexivity.
  Qed.

Search beq_nat.


Theorem S_inj : forall (n m : nat)(b:bool),
  beq_nat (S n) (S m) = b ->
  beq_nat n m = b.
Proof.
  intros n m b H.
  simpl in H. apply H. Qed.

Theorem silly3' : forall (n : nat),
  (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
  true = beq_nat n 5 ->
  true = beq_nat (S (S n)) 7.
Proof.
  intros n eq H.
  symmetry in H.
  apply eq in H.
  symmetry in H.
  apply H.
  Qed.

Search plus_n_Sm.

Theorem plus_n_n_injective : forall n m,
  n + n = m + m ->
  n = m.
Proof.
  intros n. induction n as [| n'].
  - intros m. intros H. simpl in H.
  Admitted.

Theorem double_injective: forall n m,
  double n = double m -> n = m.
Proof.
  intros n. induction n as [| n'].
  - simpl. intros m eq. destruct m as [| m'].
   + reflexivity.
   + inversion eq.
  - simpl. intros m eq. destruct m as [| m'].
   + simpl. inversion eq.
   + apply f_equal.
    apply IHn'. inversion eq. reflexivity.
    Qed.