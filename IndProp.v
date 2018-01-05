Set Warnings "-notation-overridden,-parsing".
Require Coq.omega.Omega.
Require Import Coq.omega.Omega.
Require Export Logic.

Inductive ev : nat->Prop :=
  | ev_0 : ev 0
  | ev_SS : forall n : nat, ev n -> ev (S (S n)).

Theorem ev_4: ev 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0.
  Qed.

Theorem ev_4': ev 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.

Theorem ev_plus4: forall n, ev n -> ev (4+n).
Proof.
  intros n. simpl. intros Hn.
  apply ev_SS. apply ev_SS. apply Hn.
  Qed.

(* Exercise ev_double *)
Theorem ev_double: forall n,
  ev (double n).
Proof.
  intros n. induction n as [| n' IHn'].
  - simpl. apply ev_0.
  - simpl. apply ev_SS. apply IHn'.
  Qed.

Theorem ev_minus2: forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  inversion E as [| n' E'].
  - simpl. apply ev_0.
  - simpl. apply E'.
  Qed.

Theorem evSS_ev: forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.
  inversion E.
  apply H0.
  Qed.

Theorem one_not_even: ~ev 1.
Proof.
  intros H. inversion H. Qed.

(* Exercise inversion_practice *)
Theorem SSSSev__even: forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n H. inversion H.
  inversion H1.
  apply H3.
  Qed.

Theorem even5_nonsense: 
  ev 5 -> 2 + 2 = 9.
Proof.
  intros H. inversion H.
  inversion H1. inversion H3.
  Qed.

Lemma ev_even: forall n,
  ev n -> exists k, n = double k.
Proof.
  intros n E.
  induction E as [| n' E' IH].
  - exists 0. reflexivity.
  - destruct IH as [k' HK'].
  rewrite HK'. exists (S k'). reflexivity.
  Qed.


Theorem ev_even_iff: forall n,
  ev n <-> exists k, n = double k.
Proof.
  intros n. split.
  - apply ev_even.
  - intros [k HK]. rewrite HK.
  apply ev_double.
  Qed.

(* Exercise ev_sum *)
Theorem ev_sum: forall n m,
  ev n -> ev m -> ev (n + m).
Proof.
  intros n m eqn eqm.
  induction eqn as [| n' eqn' IHN].
  - simpl. apply eqm.
  - simpl. apply ev_SS. apply IHN.
  Qed.

(* Exercise ev_alternate *)
Inductive ev' : nat->Prop := 
  | ev'_0 : ev' 0
  | ev'_2 : ev' 2
  | ev'_sum : forall n m,
    ev' n -> ev' m -> ev' (n+m).

Lemma add_two: forall n,
  n + 2 = S (S n).
Proof. intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
  Qed.

Theorem ev'_ev : forall n,
  ev' n <-> ev n.
Proof.
  intros n. split.
  - intros H. 
  induction H as [| |n' m' IHN'].
    + apply ev_0.
    + apply ev_SS. apply ev_0.
    + apply ev_sum.
      ++ apply IHIHN'.
      ++ apply IHev'1.
  - intros H. 
  induction H as [| n' IHN].
    + apply ev'_0.
    + rewrite <- add_two.
    apply ev'_sum.
    apply IHIHN.
    apply ev'_2.
  Qed.

(* Exercise ev_ev__ev *)
Theorem ev_ev__ev: forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
  intros n m eqnm eqn.
  induction eqn as [| n' IHN].
  - simpl in eqnm. apply eqnm.
  - simpl in eqnm. inversion eqnm.
  apply IHIHN in H0.
  apply H0.
  Qed.

Lemma double_distr: forall n m,
  double (n+m) = double n + double m.
Proof.
  intros n m.
  induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'.
  reflexivity.
  Qed.

Theorem plus_cancel: forall a b c,
  a + (b + c) = a + b + c.
Proof.
  intros a b c.
  rewrite -> plus_assoc.
  reflexivity.
  Qed.

(* Exercise ev_plus_plus *)
Theorem ev_plus_plus: forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  intros n m p eqnm eqnp.
  assert(H1:ev (n+m+(n+p))).
  { apply ev_sum with (n:=n+m)(m:=n+p). 
    - apply eqnm. - apply eqnp. }
  assert(H2:n+m+(n+p)=n+m+n+p).
  { apply plus_cancel with (a:=n+m)(b:=n)(c:=p). }
  rewrite H2 in H1.
  assert(H3:n+m+n+p=n+n+m+p).
  { 
    omega. }
  rewrite H3 in H1.
  apply ev_ev__ev with (n:=n+n)(m:=m+p).
  - rewrite <- (plus_assoc (n+n) m p) in H1.
    apply H1.
  - apply ev_even_iff.
    exists n. rewrite -> double_plus.
    reflexivity.
  Qed.
  

Module Playground.

Inductive le : nat->nat->Prop := 
  | le_n : forall n, le n n
  | le_S : forall n m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).

Theorem test_le1:
  3 <= 3.
Proof.
  apply le_n. Qed.

Theorem test_le2:
  3 <= 6.
Proof.
  apply le_S. apply le_S. apply le_S. apply le_n.
  Qed.

Theorem test_le3:
  (2 <= 1) -> 2 + 2 = 5.
Proof.
  intros H. inversion H. inversion H2.
  Qed.

End Playground.

Definition lt(n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

Inductive square_of : nat->nat->Prop :=
  | sq : forall n:nat, square_of n (n*n).

Inductive next_nat : nat->nat->Prop :=
  | nn : forall n:nat, next_nat n (S n).

Inductive next_even : nat->nat->Prop :=
  | ne_1 : forall n, ev (S n) -> next_even n (S n)
  | ne_2 : forall n, ev (S (S n)) -> next_even n (S (S n)).


(* Exercise le_exercise *)
Lemma le_trans: forall m n o,
  m<=n -> n<=o -> m<=o.
Proof.
  intros m n o lemn leno.
  induction leno as [| n' o' H].
  - apply lemn.
  - apply le_S. apply H.
  Qed.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros n. induction n as [| n' H].
  - apply le_n.
  - apply le_S in H. apply H.
  Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n<=m -> S n <= S m.
Proof.
  intros n m eq. induction eq.
  - apply le_n.
  - apply le_S. apply IHeq.
  Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros n m eq. inversion eq.
  - apply le_n.
  - apply le_trans with (m:=n)(n:=(S n))(o:=m).
    + apply le_S. reflexivity.
    + apply H0.
  Qed.

Theorem le_plus_l: forall a b,
  a <= a + b.
Proof.
  intros a b.
  induction a as [| a'].
  - simpl. apply O_le_n.
  - simpl. apply n_le_m__Sn_le_Sm.
  apply IHa'.
  Qed.

Theorem plus_lt: forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
  unfold lt.
  intros n1 n2 m eq1. split.
  - assert (n1 <= n1+n2).
  { apply le_plus_l with (a:=n1)(b:=n2). }
  apply n_le_m__Sn_le_Sm in H.
  apply le_trans with (m:=S n1)(n:=S (n1+n2))(o:=m).
  + apply H.
  + apply eq1.
  - assert (n2 <= n2+n1).
  { apply le_plus_l with (a:=n2)(b:=n1). }
  rewrite plus_comm in H.
  apply n_le_m__Sn_le_Sm in H.
  apply le_trans with (m:=S n2)(n:=S (n1+n2))(o:=m).
  + apply H.
  + apply eq1.
  Qed.

Theorem lt_S: forall n m,
  n < m ->
  n < S m.
Proof.
  unfold lt. intros n m eq.
  apply le_S in eq. apply eq.
  Qed.


Theorem leb_complete: forall n m,
  leb n m = true -> 
  n <= m.
Proof.
  intros n m eq.
  generalize dependent m.
  induction n as [| n'].
  - intros n eq. apply O_le_n.
  - induction m as [| m'].
    + intros eq. simpl in eq. inversion eq.
    + intros eq. simpl in eq.
    apply IHn' in eq.
    apply n_le_m__Sn_le_Sm in eq.
    apply eq.
  Qed.

Theorem leb_refl : forall n,
  leb n n = true.
Proof.
  induction n as [|n'].
  - simpl. reflexivity.
  - simpl. apply IHn'.
  Qed.

Theorem n_leb_m__n_leb_Sm : forall n m,
  leb n m = true ->
  leb n (S m) = true.
Proof.
  intros n m eq.
  generalize dependent m.
  induction n as [|n'].
  - intros m eq. simpl. reflexivity.
  - intros m eq. simpl. induction m as [|m'].
    + simpl in eq. inversion eq.
    + simpl in eq. apply IHn' in eq.
    apply eq.
  Qed.

Theorem leb_correct : forall n m,
  n <= m ->
  leb n m = true.
Proof.
  intros n m eq.
  generalize dependent n.
  induction m as [|m'].
  - intros n eq. inversion eq. simpl. reflexivity.
  - intros n eq. inversion eq.
    + simpl. apply leb_refl.
    + apply IHm' in H0. 
    apply n_leb_m__n_leb_Sm.
    apply H0.
  Qed.

Theorem leb_true_trans : forall n m o,
  leb n m = true ->
  leb m o = true ->
  leb n o = true.
Proof.
  intros n m o eqnm eqmoo.
  apply leb_complete in eqnm.
  apply leb_complete in eqmoo.
  assert(H:n<=o).
  { apply le_trans with (m:=n)(n:=m)(o:=o).
    apply eqnm. apply eqmoo. }
  apply leb_correct in H.
  apply H.
  Qed.

(* Exercise leb_iff *)
Theorem leb_iff : forall n m,
  leb n m = true <-> n <= m.
Proof.
  intros n m. split.
  - apply leb_complete.
  - intros eq. apply leb_correct.
  apply eq.
  Qed.

Module R.

(* Exercise R_provability *)
Inductive R : nat->nat->nat->Prop :=
  | c1: R 0 0 0 
  | c2: forall m n o, R m n o -> R (S m) n (S o)
  | c3: forall m n o, R m n o -> R m (S n) (S o)
  | c4: forall m n o, R (S m) (S n) (S (S o)) -> R m n o
  | c5: forall m n o, R m n o -> R n m o.

Example prov1: (R 1 1 2).
Proof.
  apply c2.
  apply c3.
  apply c1.
  Qed.

Example prov2: (R 2 2 6).
Proof.
  Admitted.

(* Exercise R_fact *)
Definition fR:nat->nat->nat :=
  fun a =>
    fun b =>
      a + b.

Theorem R_equiv_fR: forall m n o,
  R m n o <-> fR m n = o.
Proof.
  intros m n o.
  split.
  - intros eqR. unfold fR.
  induction eqR.
    + reflexivity.
    + simpl. rewrite IHeqR. reflexivity.
    + rewrite <- IHeqR. rewrite <- plus_n_Sm.
      reflexivity.
    + simpl in IHeqR. inversion IHeqR.
    rewrite <- plus_n_Sm in H0.
    inversion H0.
    reflexivity.
    + rewrite -> plus_comm in IHeqR. 
    apply IHeqR.
  - generalize dependent o.
    unfold fR.
    induction m as [|m IHm'].
    + induction n as [|n IHn'].
      * simpl in *. 
        intros o eq. rewrite <- eq. apply c1.
      * intros o eq. simpl in *.
        rewrite <- eq.
        apply c3. apply IHn'. reflexivity.
    + induction n as [|n IHn'].
      * simpl in *. 
        intros o eq.
        rewrite -> plus_comm in eq.
        simpl in *. rewrite <- eq.
        apply c2. apply IHm'.
        rewrite -> plus_comm. simpl.
        reflexivity.
      * intros o eq.
        simpl in eq. rewrite <- plus_n_Sm in eq.
        rewrite <-  eq.
        apply c2. apply IHm'.
        rewrite <- plus_n_Sm.
        reflexivity.
  Qed.


End R.

(* Exercise subsequence *)



(* Exercise R_provability2 *)

Inductive R:nat->list nat->Prop :=
  | c1: R 0 []
  | c2: forall n l, 
      R n l ->
      R (S n) (n::l)  
  | c3: forall n l,
      R (S n) l ->
      R n l.

Example Rlist_prov1: R 2 [1;0].
Proof.
  apply c2. apply c2. apply c1.
  Qed.

Example Rlist_prov2: R 1 [1;2;1;0].
Proof.
  apply c3. apply c2. apply c3. apply c3.
  apply c2. apply c2. apply c2. apply c1.
  Qed.

Example Rlist_prov3: R 6 [3;2;1;0].
Proof.
  Admitted.

Inductive reg_exp{T:Type} : Type :=
  | EmptySet : reg_exp
  | EmptyStr : reg_exp
  | Char : T->reg_exp
  | App: reg_exp->reg_exp->reg_exp
  | Union: reg_exp->reg_exp->reg_exp
  | Star: reg_exp->reg_exp.

 Inductive exp_match {T} : list T -> reg_exp -> Prop :=
| MEmpty : exp_match [] EmptyStr
| MChar : forall x, exp_match [x] (Char x)
| MApp : forall s1 re1 s2 re2,
           exp_match s1 re1 ->
           exp_match s2 re2 ->
           exp_match (s1 ++ s2) (App re1 re2)
| MUnionL : forall s1 re1 re2,
              exp_match s1 re1 ->
              exp_match s1 (Union re1 re2)
| MUnionR : forall re1 s2 re2,
              exp_match s2 re2 ->
              exp_match s2 (Union re1 re2)
| MStar0 : forall re, exp_match [] (Star re)
| MStarApp : forall s1 s2 re,
               exp_match s1 re ->
               exp_match s2 (Star re) ->
               exp_match (s1 ++ s2) (Star re).

 Notation "s =~ re" := (exp_match s re) (at level 80).

Example reg_exp_ex1: [1] =~ Char 1.
Proof.
  apply MChar.
  Qed.

Example reg_exp_ex2: [1;2] =~ App (Char 1) (Char 2).
Proof.
  apply (MApp [1] _ [2]).
  - apply MChar.
  - apply MChar.
  Qed.

Example reg_exp_ex3: ~([1;2] =~ Char 1).
Proof.
  intros H. inversion H.
  Qed.

Fixpoint reg_exp_of_list{T}(l:list T) :=
  match l with 
  | [] => EmptyStr
  | x::l' => App (Char x) (reg_exp_of_list l')
  end.

Example reg_exp_ex4: [1;2;3] =~ reg_exp_of_list [1;2;3].
Proof.
  simpl. apply (MApp [1]).
  { apply MChar. }
  apply (MApp [2]).
  { apply MChar. }
  apply (MApp [3]).
  { apply MChar. }
  apply MEmpty.
  Qed.

Lemma MStar1:
  forall T s (re:@reg_exp T),
  s =~ re ->
  s =~ Star re.
Proof.
  intros T s re H.
  rewrite <- (app_nil_r _ s).
  apply (MStarApp s [] re).
  - apply H.
  - apply MStar0.
  Qed.

(* Exercise exp_match_ex1 *)
Lemma empty_is_empty: forall T (s:list T),
  ~(s =~ EmptySet).
Proof.
  intros T s. unfold not. intros eq.
  inversion eq.
  Qed.

Lemma MUnion': forall T (s:list T)
  (re1 re2 : @reg_exp T),
  s =~ re1 \/ s =~ re2 ->
  s =~ Union re1 re2.
Proof.
  intros T s re1 re2 [H | H].
  - apply MUnionL. apply H.
  - apply MUnionR. apply H.
  Qed.

Lemma MStar': forall T (ss:list (list T))
  (re:reg_exp),
  (forall s, In s ss -> s =~ re) ->
  fold app ss [] =~ Star re.
Proof.
  intros T ss re eq.
  induction ss as [|hh tt IHs'].
  - simpl. apply MStar0.
  - simpl. Admitted.

(* Exercise reg_exp_of_list *)
Lemma reg_exp_of_list_spec: forall T (s1 s2:list T),
  s1 =~ reg_exp_of_list s2 <-> s1 = s2.
Proof. 
  intros T s1 s2. split.
  - intros eq. induction s2 as [|hh tt IHs'].
    + simpl in eq. inversion eq. reflexivity.
    + simpl in *. Admitted.

Fixpoint re_chars{T}(re:reg_exp) : list T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re
  end.

Theorem in_re_match: forall T (s:list T)
  (re:reg_exp)(x:T),
  s =~ re ->
  In x s ->
  In x (re_chars re).
Proof.
  intros T s re x Hmatch Hin.
  induction Hmatch
    as [
        |x'
        |s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        |re |s1 s2 re Hmatch1 IH1 Hmatch2 IH2        
        ].
  - simpl. apply Hin.
  - simpl. simpl in Hin. apply Hin.
  - simpl. rewrite in_app_iff in *.
    destruct Hin as [Hin | Hin].
    + left. apply (IH1 Hin).
    + right. apply (IH2 Hin).
  - simpl. rewrite in_app_iff.
  left. apply (IH Hin).
  - simpl. rewrite in_app_iff.
  right. apply (IH Hin).
  - simpl. inversion Hin.
  - simpl. apply in_app_iff in Hin.
    destruct Hin as [Hin | Hin].
    + apply (IH1 Hin).
    + apply (IH2 Hin).
  Qed.

(* Exercise re_not_empty *)


Lemma star_app: forall T (s1 s2 : list T)
  (re:@reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re'.
  generalize dependent s2.
  induction H1.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
  intros s2 H. simpl. apply H.
  - inversion Heqre'.
  rewrite H0 in *.
  intros ss2 H1.
  rewrite <- app_assoc. 
  apply MStarApp.
  + apply H1_.
  + apply ((IHexp_match2 Heqre') ss2).
  apply H1.
  Qed.

(* Exercise exp_match_ex2 *)

(* Exercise pumping *)

Theorem filter_not_empty_In: forall n l,
  filter (beq_nat n) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - simpl. intros H. apply H. reflexivity.
  - simpl. destruct (beq_nat n m) eqn:H.
    + intros _.
      rewrite beq_nat_true_iff in H.
      left. symmetry. apply H.
    + intros H'. right. apply IHl'. apply H'.
  Qed.

Module FirstTry.

Inductive reflect: Prop->bool->Prop :=
  | ReflectT: forall(P:Prop), P->reflect P true
  | ReflectF: forall(P:Prop), ~P->reflect P false.

End FirstTry.

Inductive reflect(P:Prop): bool->Prop :=
  | ReflectT: P->reflect P true
  | ReflectF: ~P->reflect P false.

Theorem iff_reflect: forall P b,
  (P <-> b=true) ->
  reflect P b.
Proof.
  intros P b eq. destruct b.
  - apply ReflectT. apply eq. reflexivity.
  - apply ReflectF. unfold not. intros HP.
  apply eq in HP. inversion HP.
  Qed.

(* Exercise reflect_iff *)
Theorem reflect_iff: forall P b,
  reflect P b -> (P <-> b = true).
Proof.
  intros P b eq.
  destruct b.
  - split.
    + intros HP. reflexivity.
    + intros _. inversion eq. apply H.
  - split.
    + intros HP. inversion eq. apply H in HP.
    inversion HP.
    + intros HFalse. inversion HFalse.
  Qed.

Lemma beq_natP: forall n m,
  reflect (n=m) (beq_nat n m).
Proof.
  intros n m. apply iff_reflect.
  rewrite beq_nat_true_iff.
  reflexivity.
  Qed.

Theorem filter_not_empty_In': forall n l,
  filter (beq_nat n) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - simpl. intros H. apply H. reflexivity.
  - simpl. destruct (beq_natP n m) as [H | H].
    + intros _. rewrite H. left. reflexivity.
    + intros H'. right. apply IHl'. apply H'.
  Qed.

(* Exercise beq_natP_practice *)
Fixpoint count n l :=
  match l with
  | [] => 0
  | m::l' =>
    (if beq_nat n m then 1 else 0) + count n l'
  end.

Theorem beq_natP_practice' : forall n l,
  count n l = 0 ->
  ~(In n l).
Proof. unfold not.
    intros n l eq.
    induction l as [|hh tt IHl'].
    - simpl. intros F. apply F.
    - simpl. intros [H|H].
      + rewrite H in *. apply IHl'.
        simpl in *.
        Search beq_nat.
        rewrite Induction.beq_nat_refl in eq.
        inversion eq.
        simpl in eq.
        rewrite Induction.beq_nat_refl in eq.
        inversion eq.
      + apply IHl'.
        simpl in *.
        destruct (beq_nat n hh).
        * inversion eq.
        * simpl in eq. apply eq.
        * apply H.
  Qed.

Theorem beq_natP_practice : forall n l,
  count n l = 0 ->
  ~(In n l).
Proof.
  unfold not. intros n l. induction l as [|m l' IHl'].
  - simpl. intros _ F. apply F.
  - simpl in *. destruct (beq_natP n m) as [H|H].
    + intros eq [H1|H1].
      * inversion eq.
      * inversion eq.
    + simpl in *. intros eq [H1|H1].
      * rewrite H1 in H. apply H. reflexivity.
      * apply IHl' in eq. 
        ** apply eq.
        ** apply H1.
  Qed.

(* Exercise nostutter *)

(* Exercise filter_challenge *)

(* Exercise filter_challenge2 *)

(* Exercise palindromes *)

(* Exercise palindrome_converse *)

(* Exercise NoDup *)

(* Exercise pigeonhole principle *)