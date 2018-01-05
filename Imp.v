Set Warnings "-notation-overridden,-parsing".
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Import ListNotations.
Require Import Maps.

Module AExp.

Inductive aexp : Type :=
  | ANum: nat->aexp
  | APlus: aexp->aexp->aexp
  | AMinus: aexp->aexp->aexp
  | AMult: aexp->aexp->aexp.

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq: aexp->aexp->bexp
  | BLe: aexp->aexp->bexp
  | BNot: bexp->bexp
  | BAnd: bexp->bexp->bexp.


Fixpoint aeval(a:aexp) : nat :=
  match a with 
  | ANum n => n
  | APlus a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2 => (aeval a1) - (aeval a2)
  | AMult a1 a2 => (aeval a1) * (aeval a2)
  end.

Example test_aeval1:
  aeval (APlus (ANum 2) (ANum 2)) = 4.
Proof.
  reflexivity. Qed.

Fixpoint beval(b:bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => beq_nat (aeval a1) (aeval a2)
  | BLe a1 a2 => leb (aeval a1) (aeval a2)
  | BNot b1 => negb (beval b1)
  | BAnd b1 b2 => andb (beval b1) (beval b2)
  end.

Fixpoint optimize_0plus(a:aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus (ANum 0) e2 => 
    optimize_0plus e2
  | APlus e1 e2 =>
    APlus (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 =>
    AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult e1 e2 =>
    AMult (optimize_0plus e1) (optimize_0plus e2)
  end.

Example test_optimize_0plus:
  optimize_0plus (APlus (ANum 2)
                        (APlus (ANum 0)
                               (APlus (ANum 0) (ANum 1))))
  = APlus (ANum 2) (ANum 1).
Proof.
  reflexivity.
  Qed.

Theorem optimize_0plus_sound: forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a. induction a.
  - reflexivity.
  - destruct a1.
    + destruct n.
      * simpl. apply IHa2.
      * simpl. rewrite IHa2. reflexivity.
    + simpl. simpl in IHa1. rewrite IHa1.
    rewrite IHa2. reflexivity.
    + simpl. simpl in IHa1. rewrite IHa1.
    rewrite IHa2. reflexivity.
    + simpl. simpl in IHa1. rewrite IHa1.
    rewrite IHa2. reflexivity.
  - simpl. rewrite IHa1. rewrite IHa2.
  reflexivity.
  - simpl. rewrite IHa1. rewrite IHa2.
  reflexivity.
  Qed.

Theorem silly1: forall ae, aeval ae = aeval ae.
Proof. try reflexivity. Qed.

Theorem silly2: forall (P:Prop), P->P.
Proof.
  intros P HP.
  try reflexivity. apply HP.
  Qed.

Lemma foo : forall n, leb 0 n = true.
Proof.
  intros. destruct n.
  - simpl. reflexivity.
  - simpl. reflexivity.
  Qed.

Lemma foo': forall n, leb 0 n = true.
Proof.
  intros. destruct n; simpl; reflexivity.
  Qed.

Theorem optimize_0plus_sound': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a; 
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity).
  - reflexivity.
  - destruct a1;
    try (simpl; simpl in IHa1; rewrite IHa1;
        rewrite IHa2; reflexivity).
    + destruct n; simpl; rewrite IHa2;
      reflexivity.
  Qed.

Theorem In10: In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (try (left; reflexivity); right).
  Qed.

(* Exercise optimize_0plus_b *)

Tactic Notation "simpl_and_try" tactic(c) :=
  simpl;
  try c.

Example silly_presburger_example: forall m n o p,
  m+n <= n+o /\ o+3=p+3 ->
  m <= p.
Proof.
  intros. omega.
  Qed.

Module aevalR_first_try.

Inductive aevalR: aexp->nat->Prop :=
  | E_ANum: forall (n:nat),
    aevalR (ANum n) n
  | E_APlus: forall (e1 e2 : aexp)(n1 n2 : nat),
    aevalR e1 n1 ->
    aevalR e2 n2 ->
    aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus: forall (e1 e2 : aexp)(n1 n2 : nat),
    aevalR e1 n1 ->
    aevalR e2 n2 ->
    aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult: forall (e1 e2 : aexp)(n1 n2 : nat),
    aevalR e1 n1 ->
    aevalR e2 n2 ->
    aevalR (AMult e1 e2) (n1 * n2).

Notation "e '\\' n"
         := (aevalR e n)
            (at level 50, left associativity)
         : type_scope.

End aevalR_first_try.

Reserved Notation "e '\\' n" (at level 50, left associativity).
Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum : forall (n:nat),
      (ANum n) \\ n
  | E_APlus : forall (e1 e2: aexp) (n1 n2 : nat),
      (e1 \\ n1) -> (e2 \\ n2) -> (APlus e1 e2) \\ (n1 + n2)
  | E_AMinus : forall (e1 e2: aexp) (n1 n2 : nat),
      (e1 \\ n1) -> (e2 \\ n2) -> (AMinus e1 e2) \\ (n1 - n2)
  | E_AMult : forall (e1 e2: aexp) (n1 n2 : nat),
      (e1 \\ n1) -> (e2 \\ n2) -> (AMult e1 e2) \\ (n1 * n2)

  where "e '\\' n" := (aevalR e n) : type_scope.

Theorem aeval_iff_aevalR: forall a n,
  (a \\ n) <-> aeval a = n.
Proof.
  intros a n. split.
  - intros H. induction H;
  try (simpl; rewrite IHaevalR1; rewrite IHaevalR2; reflexivity);
  try reflexivity.
  - intros H. induction H. induction a.
    + simpl. apply E_ANum.
    + simpl. apply E_APlus.
      apply IHa1. apply IHa2.
    + simpl. apply E_AMinus.
      apply IHa1. apply IHa2.
    + simpl. apply E_AMult.
      apply IHa1. apply IHa2.
  Qed.

(* Exercise bevalR *)
Inductive bevalR: bexp->bool->Prop :=
  | E_BTrue: bevalR BTrue true
  | E_BFalse: bevalR BFalse false
  | E_BEq: forall (e1 e2:aexp)(n1 n2:nat),
         aevalR e1 n1 ->
         aevalR e2 n2 ->
          bevalR (BEq e1 e2) (beq_nat n1 n2)
  | E_BLe: forall (e1 e2:aexp)(n1 n2:nat),
         aevalR e1 n1 ->
         aevalR e2 n2 ->
          bevalR (BLe e1 e2) (leb n1 n2)
  | E_BNot: forall (e1:bexp)(n1:bool),
          bevalR e1 n1 ->
            bevalR (BNot e1) (negb n1)
  | E_BAnd: forall (e1 e2:bexp)(n1 n2:bool),
          bevalR e1 n1 ->
          bevalR e2 n2 ->
           bevalR (BAnd e1 e2) (andb n1 n2).

Lemma beval_iff_bevalR: forall b bv,
  bevalR b bv <-> beval b = bv.
Proof.
  intros b bv. split.
  - intros H. induction H.
    + reflexivity.
    + reflexivity.
    + simpl. apply aeval_iff_aevalR in H.
    apply aeval_iff_aevalR in H0.
    rewrite H. rewrite H0. reflexivity.
    + simpl. rewrite aeval_iff_aevalR in H.
    apply aeval_iff_aevalR in H0.
    rewrite H. rewrite H0. reflexivity.
    + simpl. rewrite IHbevalR. reflexivity.
    + simpl. rewrite IHbevalR1. rewrite IHbevalR2.
    reflexivity.
  - intros H. induction H. induction b.
    + apply E_BTrue.
    + apply E_BFalse.
    + apply E_BEq.
      * induction a.
        ** apply E_ANum.
        ** simpl. apply E_APlus.
        apply IHa1. apply IHa2. 
        ** simpl. apply E_AMinus.
        apply IHa1. apply IHa2.
        ** simpl. apply E_AMult.
        apply IHa1. apply IHa2.
      * induction a0;
        try (simpl; apply aeval_iff_aevalR;
        simpl; reflexivity);
        try reflexivity.
   + apply E_BLe.
        * induction a.
        ** apply E_ANum.
        ** simpl. apply E_APlus.
        apply IHa1. apply IHa2. 
        ** simpl. apply E_AMinus.
        apply IHa1. apply IHa2.
        ** simpl. apply E_AMult.
        apply IHa1. apply IHa2.
      * induction a0;
        try (simpl; apply aeval_iff_aevalR;
        simpl; reflexivity);
        try reflexivity.
  + simpl. apply E_BNot. apply IHb.
  + simpl. apply E_BAnd. apply IHb1.
    apply IHb2.
  Qed.

End AExp.

Module aevalR_division.

Inductive aexp : Type := 
  | ANum: nat->aexp
  | APlus: aexp->aexp->aexp
  | AMinus: aexp->aexp->aexp
  | AMult: aexp->aexp->aexp
  | ADiv: aexp->aexp->aexp.

Reserved Notation "e '\\' n"
        (at level 50, left associativity).

Inductive aevalR: aexp->nat->Prop :=
  | E_ANum : forall (n:nat),
        (ANum n) \\ n
  | E_APlus: forall (a1 a2 : aexp)(n1 n2 : nat),
        (a1 \\ n1) ->
        (a2 \\ n2) ->
        (APlus a1 a2) \\ (n1 + n2)
  | E_AMinus: forall (a1 a2 : aexp)(n1 n2 : nat),
        (a1 \\ n1) ->
        (a2 \\ n2) ->
        (AMinus a1 a2) \\ (n1 - n2)
  | E_AMult: forall (a1 a2 : aexp)(n1 n2 : nat),
        (a1 \\ n1) ->
        (a2 \\ n2) ->
        (AMult a1 a2) \\ (n1 * n2)
  | E_ADiv: forall (a1 a2 : aexp)(n1 n2 n3 : nat),
        (a1 \\ n1) ->
        (a2 \\ n2) ->
        (n2 > 0) ->
        (mult n2 n3 = n1) ->
        (ADiv a1 a2) \\ n3
where "a '\\' n" := (aevalR a n) : type_scope.

End aevalR_division.

Module aevalR_extended.

 Reserved Notation "e '\\' n" (at level 50, left associativity).
Inductive aexp : Type :=
  | AAny : aexp (* <--- NEW *)
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Inductive aevalR : aexp -> nat -> Prop :=
  | E_Any : forall (n:nat),
      AAny \\ n (* <--- new *)
  | E_ANum : forall (n:nat),
      (ANum n) \\ n
  | E_APlus : forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 \\ n1) -> (a2 \\ n2) -> (APlus a1 a2) \\ (n1 + n2)
  | E_AMinus : forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 \\ n1) -> (a2 \\ n2) -> (AMinus a1 a2) \\ (n1 - n2)
  | E_AMult : forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 \\ n1) -> (a2 \\ n2) -> (AMult a1 a2) \\ (n1 * n2)

where "a '\\' n" := (aevalR a n) : type_scope.

End aevalR_extended.

Definition state := total_map nat.

Definition empty_state : state :=
  t_empty 0.

 Inductive aexp : Type :=
  | ANum : nat -> aexp
  | AId : id -> aexp (* <----- NEW *)
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

 Definition W : id := Id "W".
Definition X : id := Id "X".
Definition Y : id := Id "Y".
Definition Z : id := Id "Z".

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x (* <----- NEW *)
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2 => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => beq_nat (aeval st a1) (aeval st a2)
  | BLe a1 a2 => leb (aeval st a1) (aeval st a2)
  | BNot b1 => negb (beval st b1)
  | BAnd b1 b2 => andb (beval st b1) (beval st b2)
  end.

Example aexp1 :
  aeval (t_update empty_state X 5)
        (APlus (ANum 3) (AMult (AId X) (ANum 2)))
  = 13.
Proof. reflexivity. Qed.

Example bexp1 :
  beval (t_update empty_state X 5)
        (BAnd BTrue (BNot (BLe (AId X) (ANum 4))))
  = true.
Proof. reflexivity. Qed.

 Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com.

Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).

 Definition fact_in_coq : com :=
  Z ::= AId X;;
  Y ::= ANum 1;;
  WHILE BNot (BEq (AId Z) (ANum 0)) DO
    Y ::= AMult (AId Y) (AId Z);;
    Z ::= AMinus (AId Z) (ANum 1)
  END.

 Definition plus2 : com :=
  X ::= (APlus (AId X) (ANum 2)).
Definition XtimesYinZ : com :=
  Z ::= (AMult (AId X) (AId Y)).
Definition subtract_slowly_body : com :=
  Z ::= AMinus (AId Z) (ANum 1) ;;
  X ::= AMinus (AId X) (ANum 1).

Definition subtract_slowly : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    subtract_slowly_body
  END.
Definition subtract_3_from_5_slowly : com :=
  X ::= ANum 3 ;;
  Z ::= ANum 5 ;;
  subtract_slowly.

Definition loop : com :=
  WHILE BTrue DO
    SKIP
  END.

Reserved Notation "c1 '/' st '\\' st'"
                  (at level 40, st at level 39).
Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      SKIP / st \\ st
  | E_Ass : forall st a1 n x,
      aeval st a1 = n ->
      (x ::= a1) / st \\ (t_update st x n)
  | E_Seq : forall c1 c2 st st' st'',
      c1 / st \\ st' ->
      c2 / st' \\ st'' ->
      (c1 ;; c2) / st \\ st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      c1 / st \\ st' ->
      (IFB b THEN c1 ELSE c2 FI) / st \\ st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      c2 / st \\ st' ->
      (IFB b THEN c1 ELSE c2 FI) / st \\ st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      (WHILE b DO c END) / st \\ st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      c / st \\ st' ->
      (WHILE b DO c END) / st' \\ st'' ->
      (WHILE b DO c END) / st \\ st''

  where "c1 '/' st '\\' st'" := (ceval c1 st st').

Example ceval_example1:
    (X ::= ANum 2;;
     IFB BLe (AId X) (ANum 1)
       THEN Y ::= ANum 3
       ELSE Z ::= ANum 4
     FI)
   / empty_state
   \\ (t_update (t_update empty_state X 2) Z 4).
Proof.
  apply E_Seq with (t_update empty_state X 2).
  - apply E_Ass. reflexivity.
  - apply E_IfFalse.
    + reflexivity.
    + apply E_Ass. reflexivity.
  Qed.

(* Exercise ceval_example2 *)
Example ceval_example2: 
  (X ::= ANum 0;; Y ::= ANum 1;; 
   Z ::= ANum 2) / empty_state \\
  (t_update (t_update (t_update empty_state X 0) Y 1) Z 2).
Proof.
  apply E_Seq with (t_update empty_state X 0).
  - apply E_Ass. simpl. reflexivity.
  - apply E_Seq with (t_update (t_update empty_state X 0) Y 1).
    -- apply E_Ass. simpl. reflexivity.
    -- apply E_Ass. simpl. reflexivity.
  Qed.

(* Exercise pup_to_n *)

Theorem ceval_deterministic: forall c st st1 st2,
     c / st \\ st1 ->
     c / st \\ st2 ->
     st1 = st2.
Proof. 
    intros c st st1 st2 E1 E2.
    generalize dependent st2.
    induction E1;
      intros st2 E2; inversion E2; subst.
    - reflexivity.
    - reflexivity.
    - assert(st'=st'0) as EQ1.
    { apply IHE1_1. assumption. }

Theorem plus2_spec : forall st n st',
  st X = n ->
  plus2 / st \\ st' ->
  st' X = n + 2.
Proof. Admitted.

(* Exercise XtimesYinZ_spec  *)

(* Exercise loop_never_stops *)

(* Exercise no_whilesR *)

(* Exercise no_whiles_terminating *)

(* Exercise stack_compiler *)

(* Exercise stack_compiler_correct *)

(* Exercise short_circuit *)

(* Exercise break_imp *)

(* Exercise while_break_true *)

(* Exercise ceval_deterministic *)

(* Exercise add_for_loop *)
