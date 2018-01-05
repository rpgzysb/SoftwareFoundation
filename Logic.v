 Set Warnings "-notation-overridden,-parsing".
Require Export Tactics.


Check 3=3.
Check forall n m : nat, n + m = m + n.

Definition plus_fact: Prop := 2 + 2 =4.
Check plus_fact.

Definition is_three(n:nat) : Prop := 
  n = 3.
Check is_three.
Check @eq.

 Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  split.
  - reflexivity.
  - reflexivity.
  Qed.

Lemma and_intro: forall A B : Prop,
  A->B->A/\B.
Proof.
  intros A B HA HB. split.
  - apply HA.
  - apply HB.
  Qed.

(* Exercise and_exercise *)
Example and_exercise : forall n m : nat,
  n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n m eq.
  destruct n as [| n'].
  - split. 
    + reflexivity. 
    + rewrite -> plus_comm in eq.
      rewrite <- plus_n_0 in eq.
      apply eq.
  - destruct m as [| m'].
    + rewrite <- plus_n_0 in eq.
      split.
      * apply eq.
      * reflexivity.
    + inversion eq.
  Qed.

Lemma and_example2: forall n m : nat,
  n = 0/\m=0 -> n + m = 0.
Proof.
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
  Qed.

Lemma and_example3: forall n m : nat,
  n + m = 0 -> n * m = 0.
Proof.
  intros n m H.
  assert (H':n=0/\m=0).
  { apply and_exercise. apply H. }
  destruct H' as [Hn Hm].
  rewrite Hn. reflexivity.
  Qed.

Lemma proj1: forall P Q : Prop,
  P/\Q -> P.
Proof.
  intros P Q [HP HQ].
  apply HP. Qed.

(* Exercise proj2 *)
Lemma proj2: forall P Q : Prop,
  P/\Q -> Q.
Proof.
  intros P Q [HP HQ].
  apply HQ. Qed.

Theorem and_commut: forall P Q : Prop,
  P/\Q -> Q/\P.
Proof.
  intros P Q [HP HQ].
  split.
  - apply HQ.
  - apply HP.
  Qed.

(* Exercise and_assoc *)
Theorem and_assoc: forall P Q R : Prop,
  P/\(Q/\R) -> (P/\Q)/\R.
Proof.
  intros P Q R [HP [HQ HR]].
  split.
  - split.
    + apply HP.
    + apply HQ.
  - apply HR.
  Qed.

Check and.

Lemma or_example: forall n m : nat,
  n = 0 \/ m=0 -> n * m = 0.
Proof.
  intros n m [Hn | Hm].
  - rewrite Hn. reflexivity.
  - rewrite Hm. rewrite <- mult_comm.
  simpl. reflexivity.
  Qed.

Lemma or_intro: forall A B : Prop,
  A -> A\/B.
Proof.
  intros A B HA.
  left.
  apply HA.
  Qed.

Lemma zero_or_succ: forall n : nat,
  n = 0 \/ n = S (pred n).
Proof.
  intros [|n].
  - left. reflexivity.
  - right. reflexivity.
  Qed.

(* Exercise mult_eq_0 *)
Lemma mult_eq_0: forall n m,
  n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m eq.
  destruct n as [| n'].
  - left. reflexivity.
  - destruct m as [| m'].
    + right. reflexivity.
    + inversion eq.
  Qed.

(* Exercise or_commut *)
Theorem or_commut: forall P Q : Prop,
  P\/Q -> Q\/P.
Proof.
  intros P Q [HP | HQ].
  - right. apply HP.
  - left. apply HQ.
  Qed.

Module MyNot.

Definition not (P:Prop) := P->False.
Notation "~ x" := (not x) : type_scope.
Check not.

End MyNot.

Theorem ex_falso_quodlibet: forall (P:Prop),
  False->P.
Proof.
  intros P contra.
  destruct contra.
  Qed.

(* Exercise not_implied_our_not *)
Fact not_implies_our_not : forall (P:Prop),
  ~P->(forall (Q:Prop), P->Q).
Proof.
  intros P HF Q.
  unfold not in HF.
  intros HP.
  apply HF in HP.
  destruct HP.
  Qed.
  

Theorem zero_not_one: ~(0=1).
Proof.
  intros contra. inversion contra.
  Qed.

Theorem zero_not_one': 0 <> 1.
Proof.
  intros H. inversion H.
  Qed.

Theorem not_False: ~False.
Proof.
  unfold not. intros H. destruct H. Qed.

Theorem contradiction_implies_anything: 
  forall P Q : Prop, (P/\~P)->Q.
Proof.
  intros P Q [HP HNA].
  unfold not in HNA.
  apply HNA in HP. destruct HP.
  Qed.

Theorem double_neg: forall P : Prop,
  P -> ~~P.
Proof.
  intros P H.
  unfold not.
  intros G. apply G in H. apply H.
  Qed.

(* Exercise contrapositive *)
Theorem contrapositivie: forall (P Q : Prop),
  (P->Q)->(~Q->~P).
Proof.
  intros P Q HL. unfold not.
  intros NQ HP.
  apply NQ in  HL.
  - apply HL.
  - apply HP.
  Qed.

(* Exercise not_both_true_and_false *)
Theorem not_both_true_and_false: 
  forall P : Prop,
  ~(P/\~P).
Proof.
  intros P. unfold not.
  intros G.
  destruct G.
  apply H0 in H. apply H.
  Qed.

Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - unfold not in H.
    apply ex_falso_quodlibet.
  apply H. reflexivity.
  - reflexivity.
  Qed.

Theorem not_true_is_false': forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - unfold not in H.
    exfalso.
  apply H. reflexivity.
  - reflexivity.
  Qed.

Lemma True_is_true: True.
Proof. apply I. Qed.

Module MyIff.

Definition iff (P Q : Prop) := 
  (P->Q)/\(Q->P).

Notation "P <-> Q" := (iff P Q)
                  (at level 95, no associativity)
                  : type_scope.

End MyIff.

Theorem iff_sym: forall P Q : Prop,
  (P<->Q) -> (Q<->P).
Proof.
  intros P Q [HAB HBA].
  split.
  - apply HBA. 
  - apply HAB.
  Qed.

Lemma not_true_iff_false: forall b,
  b <> true <-> b = false.
Proof.
  intros b. split.
  - apply not_true_is_false.
  - intros H. rewrite H. intros H'.
  inversion H'.
  Qed.

(* Exercise iff_properties *)

Theorem iff_refl: forall P : Prop,
  P <-> P.
Proof.
  intros P.
  split.
  - intros HP. apply HP.
  - intros HP. apply HP.
  Qed.

(* Exercise or_distributes_over_and *)
Theorem or_distributes_over_and: 
  forall P Q R : Prop,
  P\/(Q/\R) <-> (P\/Q)/\(P\/R).
Proof.
  intros P Q R.
  split.
  - intros [HP|[HQ HR]].
    + split.
      * apply or_intro. apply HP.
      * apply or_intro. apply HP.
    + split.
      * right. apply HQ.
      * right. apply HR.
  - intros [[HP1|HQ] [HP2|HR]].
    + left. apply HP1.
    + left. apply HP1.
    + left. apply HP2.
    + right. split.
      * apply HQ.
      * apply HR.
  Qed.

 Require Import Coq.Setoids.Setoid.

Lemma mult_0: forall n m, 
  n*m=0 <-> n=0\/m=0.
Proof.
  split.
  - apply mult_eq_0.
  - apply or_example.
  Qed.

Lemma or_assoc:
  forall P Q R : Prop,
  P\/(Q\/R) <-> (P\/Q)\/R.
Proof.
  intros P Q R. split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H|H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
  Qed.

Lemma mult_0_3 : 
  forall n m p,
  n * m * p = 0 <-> n=0\/m=0\/p=0.
Proof.
  intros n m p.
  rewrite mult_0.
  rewrite mult_0.
  rewrite or_assoc.
  reflexivity.
  Qed.

Lemma apply_iff_example:
  forall n m : nat,
  n * m = 0 -> n=0\/m=0.
Proof.
  intros n m H.
  apply mult_0.
  apply H.
  Qed.

Lemma four_is_even: exists n : nat,
  4 = n + n.
Proof.
  exists 2. reflexivity.
  Qed.

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n [m Hm].
  exists (2+m).
  apply Hm.
  Qed.

(* Exercise dist_not_exists *)
Theorem dist_not_exists: forall (X:Type)
  (P:X->Prop),
  (forall x, P x) -> ~(exists x, ~ P x).
Proof.
  intros X P H.
  unfold not.
  intros [x Ex].
  apply Ex in H.
  apply H.
  Qed.

(* Exercise dist_exists_or *)
Theorem dist_exists_or: forall (X:Type)
  (P Q : X -> Prop), 
  (exists x, P x \/ Q x) <-> 
  (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q.
  split.
  - intros [x [HP | HQ]].
    + left. exists x. apply HP.
    + right. exists x. apply HQ.
  - intros [[x H] | [x H]].
    + exists x. left. apply H.
    + exists x. right. apply H.
  Qed.

Fixpoint In{A:Type}(x:A)(l:list A) : Prop :=
  match l with 
  | [] => False
  | x'::l' => x'=x \/ In x l'
  end.

Example In_example1: In 4 [1;2;3;4;5].
Proof.
  simpl. right. right. right. left. reflexivity.
  Qed.

Example In_example2: forall n,
  In n [2;4] -> 
  exists n', n = 2 * n'.
Proof.
  simpl.
  intros n [H | [H | []]].
  - exists 1. rewrite <- H. reflexivity.
  - exists 2. rewrite <- H. reflexivity.
  Qed.

Lemma In_map:
  forall (A B : Type)(f:A->B)(l:list A)(x:A),
  In x l -> In (f x) (map f l).
  intros A B f l x.
  induction l as [| x' l' IHl'].
  - simpl. intros [].
  - simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H.
  Qed.


(* Exercise In_map_iff *)
Theorem In_map_iff:
  forall (A B : Type)(f:A->B)(l:list A)(y:B),
  In y (map f l) <->
  exists x, f x = y /\ In x l.
Proof.
  intros A B f l y.
  induction l as [| y' l' IHl'].
  - simpl. split.
    + intros F. destruct F.
    + intros [x [Fx FF]]. apply FF.
  - simpl. split.
    + intros [FY | IY].
      * exists y'. 
        split.
        ** apply FY.
        ** left. reflexivity.
      * apply IHl' in IY. 
        destruct IY.
        destruct H.
        exists x. split.
        ** apply H. 
        ** right. apply H0.
   + intros Ex. destruct Ex. destruct H. destruct H0.
      * rewrite -> H0. left. apply H.
      * right. apply IHl'.
        exists x. split.
          ** apply H.
          ** apply H0.
  Qed.

(* Exercise in_app_iff *)
Lemma in_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros A l l' a.
  split.
  - intros H. induction l as [| h t IHl'].
    + simpl. simpl in H. right. apply H.
    + simpl. destruct IHl'.
       Admitted.

(* Exercise All *)
Fixpoint All{T:Type}(P:T->Prop)(l:list T) : Prop
  := match l with 
  | [] => True
  | h::t => (P h)/\(All P t)
  end.

Lemma All_In:
  forall T (P : T->Prop)(l:list T),
  (forall x, In x l -> P x) <-> All P l.
Proof.
  intros T P l. split.
  - intros eq. induction l as [| h l' IHl'].
    + simpl. reflexivity.
    + simpl. split.
      * apply eq. 
        apply in_app_iff with (a:=h)(l:=[h]).
        left. simpl. left. reflexivity.
      * apply IHl'. intros x. intros Ix.
        apply eq.
        apply in_app_iff with (a:=x)(l:=[h]).
        right. apply Ix.
  - intros eq. induction l as [| h l' IHl'].
    + simpl. intros x. intros contra.
     destruct contra.
    + simpl. intros x. intros [Hx | Hin].
      * apply IHl'.
        ** apply eq.
        ** rewrite <- Hx. 
      Admitted.

(* Exercise combine_odd_even *)
Definition combine_odd_even (Podd Peven : nat->Prop) :
  nat->Prop := 
  fun (n:nat) => if oddb n 
                then (Podd n) 
                else (Peven n).

Theorem combine_odd_even_intro:
  forall (Podd Peven : nat->Prop)(n:nat),
  (oddb n = true -> Podd n) ->
  (oddb n = false -> Peven n) ->
  combine_odd_even Podd Peven n.
Proof.
  intros Podd Peven n HT HF.
  unfold combine_odd_even.
  destruct (oddb n).
  - apply HT. reflexivity.
  - apply HF. reflexivity.
  Qed.

Theorem combine_odd_even_elim_odd:
  forall (Podd Peven : nat->Prop)(n:nat),
  combine_odd_even Podd Peven n ->
  oddb n = true ->
  Podd n.
Proof.
  intros Podd Peven n HI HO.
  unfold combine_odd_even in HI.
  rewrite HO in HI. apply HI.
  Qed.

Theorem combine_odd_even_elim_even:
  forall (Podd Peven : nat->Prop)(n:nat),
  combine_odd_even Podd Peven n ->
  oddb n = false ->
  Peven n.
Proof.
  intros Podd Peven n HI HF.
  unfold combine_odd_even in HI.
  rewrite HF in HI. apply HI.
  Qed.

Check plus_comm.
Lemma pllus_comm3:
  forall n m p, n + (m+p) = (p+m)+n.
Proof.
  intros n m p.
  rewrite plus_comm.
  rewrite (plus_comm m).
  reflexivity.
  Qed.

Example lemma_application_ex : 
  forall {n:nat}{ns:list nat},
  In n (map (fun m => m * 0) ns) ->
  n = 0.
Proof.
  intros n ns H.
  destruct (proj1 _ _ (In_map_iff _ _ _ _ _) H)
          as [m [Hm _]].
  rewrite mult_comm in Hm. simpl in Hm.
  rewrite <- Hm. reflexivity.
  Qed.

 Example function_equality_ex1 : plus 3 = plus (pred 4).
Proof. reflexivity. Qed.

Axiom functional_extensionality:
  forall {X Y : Type}{f g : X->Y},
  (forall (x:X), f x = g x) -> f = g.

Example function_equality_ex2:
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality.
  intros x.
  apply plus_comm.
  Qed.

Print Assumptions function_equality_ex2.

(* Exercise tr_rev *)
Fixpoint rev_append{X}(l1 l2 : list X) : list X
  := match l1 with 
  | [] => l2
  | x::l1' => rev_append l1' (x::l2)
  end.

Definition tr_rev{X}(l:list X) : list X :=
  rev_append l [].

Lemma tr_rev_correct: forall X, 
  @tr_rev X = @rev X.
Proof.
  intros X.
  apply functional_extensionality.
  intros x.
  induction x as [| h t IHx'].
  - reflexivity.
  - unfold tr_rev. unfold tr_rev in IHx'.
  simpl. rewrite <- IHx'.
  Admitted.
  

Theorem evenb_double : forall k, 
  evenb (double k) = true.
Proof.
  intros k. induction k  as[| k' IHk'].
  - reflexivity.
  - simpl. apply IHk'. 
  Qed.

(* evenb_double_conv *)
Theorem evenb_double_conv : forall n,
  exists k, 
  n = if evenb n 
      then double k 
      else S (double k).
Proof.
  intros n. induction n as [|n' IHn'].
  - simpl. exists 0. reflexivity.
  - destruct (evenb n') eqn:Heq.
    + rewrite evenb_S. rewrite Heq. simpl.
    destruct IHn' as [n'' IHn''].
    exists n''. rewrite IHn''. reflexivity.
    + rewrite evenb_S. rewrite Heq. simpl.
    destruct IHn' as [n'' IHn''].
    exists (n''+1). rewrite IHn''. 
    rewrite double_plus. rewrite double_plus.
    rewrite plus_n_Sm. rewrite <- plus_1_l. rewrite <- plus_n_Sm. rewrite <- (plus_1_l (n'' + n'')).
      rewrite plus_comm. rewrite plus_assoc.  rewrite (plus_comm 1).
      rewrite plus_assoc. reflexivity.
Qed. 

Theorem even_bool_prop : forall n,
  evenb n = true <-> exists k, n = double k.
Proof.
  intros n. split.
  - intros H. destruct (evenb_double_conv n) as [k Hk].
    rewrite Hk. rewrite H. exists k. reflexivity.
  - intros [k Hk]. rewrite Hk. apply evenb_double.
  Qed.

Theorem beq_nat_true_iff: forall n1 n2 : nat,
  beq_nat n1 n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply beq_nat_true.
  - intros H. rewrite H. 
  apply beq_nat_refl.
  Qed.

Fail Definition is_even_prime n :=
  if n=2 then true else false.

Example even_1000: exists k, 1000 = double k.
Proof. exists 500. reflexivity. Qed.

(* Exercise logical_connectives *)
Lemma andb_true_iff: forall b1 b2 : bool,
  b1 && b2 = true <-> b1=true/\b2=true.
Proof.
  intros b1 b2. split.
  - intros eq. destruct b1 eqn:H.
    -- split.
      --- reflexivity.
      --- simpl in eq. apply eq.
    -- inversion eq.
  - intros [eq1 eq2].
  rewrite eq1. rewrite eq2. reflexivity.
  Qed.

Lemma orb_true_iff: forall b1 b2:bool,
  b1 || b2 = true <-> b1=true\/b2=true.
Proof.
  intros b1 b2. split.
  - intros eq. destruct b1 eqn:H.
    -- left. reflexivity.
    -- simpl in eq. right. apply eq.
  - intros [eq1 | eq2].
    -- rewrite eq1. reflexivity.
    -- rewrite eq2. destruct b1 eqn:HB.
      --- reflexivity.
      --- reflexivity.
  Qed.

(* Exercise beq_nat_false_iff *)
Theorem beq_nat_false_iff:forall x y : nat,
  beq_nat x y = false <-> x <> y.
Proof.
  intros x y. unfold not. split.
  - intros eq. intros HEQ.
  rewrite HEQ in eq. Search beq_nat.
  rewrite beq_nat_refl in eq. inversion eq.
  - intros eq. destruct (beq_nat x y) eqn:Heq.
    -- apply beq_nat_true_iff in Heq.
      apply eq in Heq. destruct Heq.
    -- reflexivity.
  Qed.

(* Exercise beq_list *)

(* Exercise All_forallb *)

Definition excluded_middle: forall P : Prop,
  P\/~P.
Proof.
  Admitted.

Theorem restricted_excluded_middle : forall P b,
  (P <-> b = true) -> P \/ ~P.
Proof.
  intros P [] H.
  - left. rewrite H. reflexivity.
  - right. rewrite H. intros contra. inversion contra.
  Qed.

Theorem restricted_excluded_middle_eq: 
  forall (n m : nat),
  n = m \/ n <> m.
Proof.
  intros n m.
  apply (restricted_excluded_middle (n=m)(beq_nat n m)).
  symmetry.
  apply beq_nat_true_iff.
  Qed.

(* Exercise excluded_middle_irrefutable *)

(* Exercise not_exists_dist *)

(* Exercise classical_axioms *)