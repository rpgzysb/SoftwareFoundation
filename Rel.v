 Set Warnings "-notation-overridden,-parsing".
Require Export IndProp.

Definition relation(X:Type) := 
  X->X->Prop.

Print le.
Check le.
Check le : relation nat.

Definition partial_function{X:Type}
  (R:relation X) :=
  forall x y1 y2 : X, 
  R x y1 -> R x y2 -> y1 = y2.

Print next_nat.
Check next_nat : relation nat.

Theorem next_nat_partial_function :
  partial_function next_nat.
Proof.
  unfold partial_function.
  intros x y1 y2 eq1 eq2.
  inversion eq1.
  inversion eq2.
  reflexivity.
  Qed.

Theorem le_not_a_partial_function :
  ~(partial_function le).
Proof.
  unfold not.
  unfold partial_function.
  intros eq.
  assert(0=1) as contra.
  { apply eq with (x:=0).
    - apply le_n.
    - apply le_S. apply le_n. }
  inversion contra.
  Qed.

Definition reflexive{X:Type}(R:relation X)
  := forall a:X, R a a.

Theorem le_reflexive: reflexive le.
Proof.
  unfold reflexive.
  intros a. apply le_n.
  Qed.

Definition transitive{X:Type}(R:relation X)
  := forall a b c : X, 
  (R a b) -> (R b c) -> (R a c).

Theorem le_trans : transitive le.
Proof.
  unfold transitive.
  intros a b c eqab eqbc.
  apply le_trans with (m:=a)(n:=b)(o:=c).
  - apply eqab.
  - apply eqbc.
  Qed.

Theorem lt_trans : transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros a b c Hnm Hmo.
  apply le_S in Hnm.
  apply le_trans with (a:=(S a))(b:=(S b))(c:=c).
  - apply Hnm.
  - apply Hmo.
  Qed.

(* Exercise le_trans_hard_way *)
Theorem lt_trans': transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction Hmo as [|m' Hm'o].
  - Print le.
    apply le_S. apply Hnm.
  - apply le_S. apply IHHm'o.
  Qed.

(* Exercise le_S_n *)
Theorem le_Sn_le: forall n m,
  S n <= m -> 
  n <= m.
Proof.
  intros n m eq.
  apply le_trans with (a:=n)(b:=S n)(c:=m).
  - apply le_S. apply le_n.
  - apply eq.
  Qed.

Theorem le_S_n: forall n m,
  (S n <= S m) -> (n <= m).
Proof.
  intros n m eq.
  Search le.
  apply Sn_le_Sm__n_le_m.
  apply eq.
  Qed.

(* Exercise le_Sn_n *)
Theorem le_Sn_n: forall n,
  ~(S n <= n).
Proof.
  unfold not. intros n eq.
  induction n as [|n' IHn'].
  - inversion eq.
  - apply Sn_le_Sm__n_le_m in eq.
  apply IHn' in eq. apply eq.
  Qed.

Definition symmetric{X:Type}(R:relation X)
  := forall a b : X,
  (R a b) -> (R b a).

(* Exercise le_not_symmetry *)
Theorem le_not_symmetric:
  ~(symmetric le).
Proof. 
  unfold symmetric. unfold not.
  intros eq. apply eq with (a:=0)(b:=S 0) in eq.
  - apply le_Sn_n in eq. apply eq.
  - assert(H:0<=S 0).
  { apply le_S. apply le_n. }
  apply eq in H. apply H.
  Qed.

Definition antisymmetric{X:Type}(R:relation X)
  := forall a b : X, 
  (R a b) -> (R b a) -> a = b.

(* Exercise le_antisymmetry *)
Lemma eq_S_n: forall n m,
  n = m ->
  S n = S m.
Proof.
  intros. rewrite H. reflexivity.
  Qed.

Theorem le_antisymmetric: antisymmetric le.
Proof.
  unfold antisymmetric.
  induction a as [|a' IHa'].
  - intros. inversion H0. reflexivity.
  - induction b as [|b' IHb'].
    + intros. inversion H.
    + intros. apply eq_S_n. apply IHa'.
      * apply le_S_n. apply H.
      * apply le_S_n. apply H0.
  Qed.

(* Exercise le_step *)
Theorem le_step : forall n m p,
  n < m ->
  m <= S p ->
  n <= p.
Proof.
  unfold lt. intros n m p eqnm eqm.
  apply le_S_n.  
  apply le_trans with (a:=S n)(b:=m)(c:=S p).
  - apply eqnm.
  - apply eqm.
  Qed.

Definition equivalence{X:Type}(R:relation X)
  := (reflexive R)/\(symmetric R)/\(transitive R).

Definition order{X:Type}(R:relation X) :=
  (reflexive R)/\(antisymmetric R)/\(transitive R).

Definition preorder{X:Type}(R:relation X) :=
  (reflexive R)/\(transitive R).

Theorem le_order : order le.
Proof. 
  unfold order. split.
  - apply le_reflexive.
  - split.
   + apply le_antisymmetric.
   + apply le_trans.
  Qed.


Inductive clos_refl_trans{A:Type}(R:relation A) 
  : relation A :=
  | rt_step: forall x y, R x y -> clos_refl_trans R x y
  | rt_refl: forall x, clos_refl_trans R x x
  | rt_trans: forall x y z,
    clos_refl_trans R x y ->
    clos_refl_trans R y z ->
    clos_refl_trans R x z.

Theorem next_nat_closure_is_le: forall n m,
  (n<=m) <-> ((clos_refl_trans next_nat) n m).
Proof.
  intros n m. split.
  - intros H. induction H.
    + apply rt_refl.
    + apply rt_trans with m.  
      * apply IHle.
      * apply rt_step. apply nn.
  - intros H. induction H.
    + inversion H. apply le_S. apply le_n.
    + apply le_n.
    + apply le_trans with y.
      * apply IHclos_refl_trans1.
      * apply IHclos_refl_trans2.
  Qed.

Inductive clos_refl_trans_ln{A:Type}
      (R:relation A)(x:A) : A->Prop 
  := 
  | rtln_refl: clos_refl_trans_ln R x x
  | rtln_trans (y z : A) :
    R x y -> 
    clos_refl_trans_ln R y z ->
    clos_refl_trans_ln R x z.

Lemma rsc_R : forall (X:Type)(R:relation X)
  (x y : X),  
  R x y -> clos_refl_trans_ln R x y.
Proof.
  intros X R x y H.
  apply rtln_trans with y.  
  - apply H.
  - apply rtln_refl.
  Qed.

(* Exercise rsc_trans *)
Lemma rsc_trans:
  forall (X:Type)(R:relation X)(x y z : X),
    clos_refl_trans_ln R x y ->
      clos_refl_trans_ln R y z ->
      clos_refl_trans_ln R x z.
Proof.
  intros X R x y z eqxy eqyz.
  induction eqxy.
  - apply eqyz.
  - apply IHeqxy in eqyz.
  apply rtln_trans with y.
    + apply H.
    + apply eqyz.
  Qed.

(* Exercise rtc_rsc_coincide *)
Theorem rtc_rsc_coincide:
  forall (X:Type)(R:relation X)(x y:X),
  clos_refl_trans R x y <-> clos_refl_trans_ln R x y.
Proof.
  intros X R x y. split.
  - intros eq.
  induction eq.
    + apply rtln_trans with y.
      * apply H.
      * apply rtln_refl.
    + apply rtln_refl.
    + apply rsc_trans with y.
      * apply IHeq1.
      * apply IHeq2.
  - intros eq.
  induction eq.
    + apply rt_refl.
    + apply rt_trans with y.
      * apply rt_step. apply H.
      * apply IHeq.
  Qed.