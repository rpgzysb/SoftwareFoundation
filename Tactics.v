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
  intros n. induction n as [| n' IHn'].
  - simpl. intros m. intros H.
  destruct m as [| m'].
    + reflexivity.
    + inversion H.
  - intros m. intros H.
  simpl in H. rewrite <- plus_n_Sm in H.
  destruct m as [| m'].
    + inversion H.
    + rewrite <- plus_n_Sm in H.
    inversion H.
    apply IHn' in H1.
    apply f_equal.
    apply H1.
  Qed.

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

(* Exercise beq_nat_ture *)
Theorem beq_nat_true : forall n m,
  beq_nat n m = true -> n = m.
Proof.
  intros n. induction n as [| n'].
  - intros m eq. destruct m as [| m'].
    + reflexivity.
    + inversion eq.
  - intros m eq. destruct m as [| m'].
    + inversion eq.
    + apply f_equal.
    apply IHn'. inversion eq.
    reflexivity.
  Qed.

Theorem double_injective_take2: forall n m,
  double n = double m -> 
  n = m.
Proof.
  intros n m.
  generalize dependent n.
  induction m as [| m'].
  - simpl. intros n eq. destruct n as [| n'].
    + reflexivity.
    + inversion eq.
  - intros n eq. destruct n as [| n'].
    + inversion eq.
    + apply f_equal. apply IHm'.
    inversion eq. reflexivity.
  Qed.

Theorem beq_id_true : forall x y,
  beq_id x y = true -> x = y.
Proof.
  intros [m] [n]. simpl. intros H.
  assert (H':m=n). { apply beq_nat_true. apply H. }
  rewrite H'. reflexivity.
  Qed.

(* Exercise gen_dep_practice *)
Theorem nth_error_after_last : forall (n:nat)
  (X:Type)(l:list X),
  length l = n ->
  nth_error l n = None.
Proof.
  intros n X l. generalize dependent n.
  induction l as [| h' l'].
  - reflexivity.
  - simpl. intros n H. induction n as [| n'].
    + inversion H.
    + simpl. apply S_injective in H.
    apply IHl' in H. apply H.
  Qed.

Definition square n := n * n.

Theorem mult_1_r: forall n : nat,
  n * 1 = n.
Proof.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
  Qed.

Theorem plus_assoc2: forall a b c : nat,
  a + (b + c) = b + (a + c).
Proof.
  intros a b c.
  assert (H1:b+c=c+b). 
  { rewrite -> plus_comm. reflexivity. }
  rewrite -> H1.
  rewrite -> plus_assoc.
  rewrite -> plus_comm.
  reflexivity.
  Qed.

Theorem mult_distr : forall n m p : nat,
  n * (m + p) = n * m + n * p.
Proof.
  intros n m p.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'.
  assert (H1:p+(n'*m+n'*p) = n'*m+(p+n'*p)).
  { rewrite -> plus_assoc2. reflexivity. }
  simpl.
  Admitted.

Theorem mult_n_Sm : forall n m : nat,
  n * m + n = n * (S m).
Proof.
  Admitted.

Theorem mult_comm : forall n m : nat,
  n * m = m * n.
Proof.
  intros n m. induction n as [| n' IHn'].
  - simpl. rewrite -> mult_0_r. reflexivity.
  - simpl. rewrite <- mult_n_Sm.
  rewrite -> IHn'.
  rewrite -> plus_comm.
  reflexivity.
  Qed.


Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros n m p.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'.
  Admitted.

Lemma square_mult : forall n m, 
  square (n * m) = (square n) * (square m).
Proof.
  intros n m.
  unfold square.
  rewrite mult_assoc.  
  assert (H : n * m * n = n * n * m).
  { rewrite mult_comm. apply mult_assoc. }
  rewrite H. rewrite mult_assoc. reflexivity.
  Qed.

Definition foo(x:nat) := 5.

Fact silly_fact_1 : forall m, 
  foo m + 1 = foo (m + 1) + 1.
Proof.
  intros m. simpl. reflexivity.
  Qed.

Definition bar x := 
  match x with 
  | O => 5
  | S _ => 5
  end.

Fact silly_fact_2' : forall m, 
  bar m + 1 = bar (m+1) + 1.
Proof.
  intros m. unfold bar.
  destruct m.
  - reflexivity.
  - reflexivity.
  Qed.

Definition sillyfun(n:nat) : bool := 
  if beq_nat n 3 then false
  else if beq_nat n 5 then false
  else false.

Theorem sillyfun_false : forall (n:nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (beq_nat n 3).
  -  reflexivity.
  - destruct (beq_nat n 5).
    + reflexivity.
    + reflexivity.
  Qed.

(* Exercise combine_split *)
Theorem combine_split: forall X Y
  (l:list (X*Y)) l1 l2,
  split l = (l1, l2) -> 
  combine l1 l2 = l.
Proof.
  intros X Y l l1 l2 eq.
  induction l as [| h t IHl].
  - simpl in eq. inversion eq.
  reflexivity.
  - destruct h. inversion eq.
  simpl. 
  Admitted.  
  

(* Exercise destruct_eqn_practice *)
Theorem bool_fn_applied_thrice :
  forall (f:bool->bool)(b:bool),
  f (f (f b)) = f b.
Proof.
  intros f b.
  destruct (f b) eqn:H1.
  - destruct b as [| b'].
    + rewrite H1. apply H1.
    + destruct (f true) eqn:Htrue.
      * apply Htrue.
      * apply H1.
  - destruct b as [| b'].
    + destruct (f false) eqn:Hfalse.
      * apply H1.
      * apply Hfalse.
    + rewrite H1. apply H1.
  Qed.
    

(* Exercise beq_nat_sym *)
Theorem beq_nat_sym: forall (n m : nat),
  beq_nat n m = beq_nat m n.
Proof.
  intros n m.
  generalize dependent m.
  induction n as [| n' IHn'].
  - destruct m as [|m'].
    + reflexivity.
    + reflexivity.
  - destruct m as [|m'].
    + reflexivity.
    + simpl. apply IHn'.
  Qed.

Theorem beq_nat_refl: forall n,
  beq_nat n n = true.

(* Exercise beq_nat_trans *)
Theorem beq_nat_trans: forall n m p,
  beq_nat n m = true ->
  beq_nat m p = true -> 
  beq_nat n p = true.
Proof. 
  intros n m p eqnm eqmp.
  apply beq_nat_true in eqnm.
  apply beq_nat_true in eqmp.
  rewrite eqnm.
  rewrite eqmp.
  apply beq_nat_refl.
  Qed.

(* Exercise split_combine *)
Definition split_combine_statement:Prop :=
  3=3.  
Admitted.

Theorem split_combine: split_combine_statement.
Proof. Admitted.

(* Exercise filter_exercise *)
Theorem filter_exercise:forall (X:Type)
  (test:X->bool)(x:X)(l lf : list X),
  filter test l = x::lf ->
  test x = true.
Proof. Admitted.

(* Exercise forall_exists_challenge *)
