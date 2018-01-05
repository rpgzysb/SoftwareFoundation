Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.

Inductive id : Type :=
  | Id : string -> id.

Definition beq_id x y :=
  match x,y with
  | Id n1, Id n2 => 
    if string_dec n1 n2
    then true
    else false
  end.

Theorem beq_id_refl: forall id, 
  true = beq_id id id.
Proof.
  intros [n]. simpl. destruct (string_dec n n).
  - reflexivity.
  - destruct n0. reflexivity.
  Qed.

Theorem beq_id_true_iff:forall x y : id,
  beq_id x y = true <-> x = y.
Proof.
  intros [n1] [n2].
  unfold beq_id.
  destruct (string_dec n1 n2).
  - subst. split. reflexivity. reflexivity.
  - split.
    + intros contra. inversion contra.
    + intros H. inversion H. subst. destruct n.
  reflexivity.
  Qed.

Theorem beq_id_false_iff: forall x y : id,
  beq_id x y = false <-> x <> y.
Proof.
  intros [n1] [n2]. unfold not. simpl.
  split.
  - intros eq. destruct (string_dec n1 n2).
    + inversion eq.
    + intros H. inversion H. subst. destruct n.
    reflexivity.
  - intros eq. destruct (string_dec n1 n2).
    + rewrite e in eq. destruct eq.
      * reflexivity. 
    + reflexivity.
  Qed.

Theorem false_beq_id: forall x y : id,
  x <> y -> beq_id x y = false.
Proof.
  unfold not. intros x y eq.
  destruct (beq_id x y) eqn:H.
  - apply beq_id_true_iff in H. 
  apply eq in H. destruct H.
  - reflexivity.
  Qed.

Definition total_map(A:Type) := id->A.

Definition t_empty{A:Type}(v:A) : total_map A 
  := (fun _ => v).

Definition t_update{A:Type}(m:total_map A)
  (x:id)(v:A) :=
  fun x' => if beq_id x x' then v else m x'.

Definition examplemap := 
  t_update (t_update (t_empty false) (Id "foo") false)
          (Id "bar") true.

 Example update_example1 : examplemap (Id "baz") = false.
Proof. reflexivity. Qed.

Example update_example2 : examplemap (Id "foo") = false.
Proof. reflexivity. Qed.

Example update_example3 : examplemap (Id "quux") = false.
Proof. reflexivity. Qed.

Example update_example4 : examplemap (Id "bar") = true.
Proof. reflexivity. Qed.

(* Exercise t_apply_empty *)
Lemma t_apply_empty : forall A x v,
  @t_empty A v x = v.
Proof.
  intros A x v.
  unfold t_empty. reflexivity.
  Qed.

(* Exercise t_update_eq *)
Lemma t_update_eq: forall A (m:total_map A) x v,
  (t_update m x v) x = v.
Proof.
  intros A m x v.
  unfold t_update.
  rewrite <- beq_id_refl. reflexivity.
  Qed.

(* Exercise t_update_neq *)
Theorem t_update_neq: forall (X:Type) v x1 x2
    (m:total_map X),
  x1 <> x2 ->
  (t_update m x1 v) x2 = m x2.
Proof.
  intros X v x1 x2 m eq.
  unfold t_update.
  apply false_beq_id in eq.
  rewrite eq. reflexivity.
  Qed.

(* Exercise t_update_shadow *)
Lemma t_update_shadow: forall A (m:total_map A)
  v1 v2 x,
  t_update (t_update m x v1) x v2
  = t_update m x v2.
Proof.
  intros A m v1 v2 x.
  unfold t_update.
  apply functional_extensionality.
  intros x0.
  destruct (beq_id x x0).
  - reflexivity.
  - reflexivity.
  Qed.

(* Exercise beq_idP *)
Lemma beq_idP: forall x y,
  reflect (x = y) (beq_id x y).
Proof.
  intros x y.
  destruct (beq_id x y) eqn:H.
  - apply beq_id_true_iff in H.
  rewrite H. apply ReflectT. reflexivity.
  - apply beq_id_false_iff in H.
  apply ReflectF. apply H.
  Qed.

(* Exercise t_update_same *)
Theorem t_update_same : forall X x (m:total_map X),
  t_update m x (m x) = m.
Proof.
  intros X x m.
  apply functional_extensionality.
  intros x0.
  unfold t_update.
  destruct (beq_idP x x0).
  - rewrite e. reflexivity.
  - reflexivity.
  Qed.

(* Exercise t_update_permute *)
Theorem t_update_permute: forall (X:Type)
  v1 v2 x1 x2 (m:total_map X),
  x2 <> x1 ->
  (t_update (t_update m x2 v2) x1 v1)
  = (t_update (t_update m x1 v1) x2 v2).
Proof.
  intros X v1 v2 x1 x2 m eq.
  apply functional_extensionality.
  intros x.
  unfold t_update.
  destruct (beq_idP x1 x).
  - destruct (beq_idP x2 x).
    + rewrite <- e0 in e. rewrite e in eq.
    destruct eq.
    reflexivity.
    + reflexivity.
  - destruct (beq_idP x2 x).
    + reflexivity.
    + reflexivity.
  Qed.

Definition partial_map (A:Type) := total_map (option A).

Definition empty {A:Type} : partial_map A :=
  t_empty None.

Definition update {A:Type} (m : partial_map A)
                  (x : id) (v : A) :=
  t_update m x (Some v).

Lemma apply_empty: forall A x, @empty A x = None.
Proof.
  intros A x. unfold empty. unfold t_empty.
  reflexivity.
  Qed.

Lemma update_eq: forall A (m:partial_map A) x v,
  (update m x v) x = Some v.
Proof.
  intros A m x v.
  unfold update. unfold t_update.
  rewrite <- beq_id_refl. reflexivity.
  Qed.

Lemma update_neq: forall (X:Type) v x1 x2
    (m:partial_map X),
  x2 <> x1 ->
  (update m x2 v) x1 = m x1.
Proof.
  intros X v x1 x2 m eq.
  unfold update. unfold t_update.
  apply beq_id_false_iff in eq.
  rewrite eq.
  reflexivity.
  Qed.

Lemma update_shadow: forall A (m:partial_map A)
  v1 v2 x,
  update (update m x v1) x v2 = update m x v2.
Proof.
  intros A m v1 v2 x. unfold update.
  unfold t_update. apply functional_extensionality.
  intros x0.
  destruct (beq_idP x x0).
  - reflexivity.
  - reflexivity.
  Qed.

Theorem update_same: forall X v x (m:partial_map X),
  m x = Some v ->
  update m x v = m.
Proof.
  intros X v x m eq. unfold update.
  unfold t_update. apply functional_extensionality.
  intros x0.
  destruct (beq_idP x x0).
  - rewrite <- eq. rewrite e. reflexivity.
  - reflexivity.
  Qed.

Theorem update_permute: forall (X:Type) v1 v2 x1 x2
  (m:partial_map X),
  x2 <> x1 ->
  (update (update m x2 v2) x1 v1) = 
  (update (update m x1 v1) x2 v2).
Proof.
  intros X v1 v2 x1 x2 m eq.
  unfold not. unfold update. unfold t_update.
  apply functional_extensionality.
  intros x.
  destruct (beq_idP x1 x).
  - destruct (beq_idP x2 x).
    + rewrite e in eq. rewrite e0 in eq.
      destruct eq. reflexivity.
    + reflexivity.
  - destruct (beq_idP x2 x).
    + reflexivity.
    + reflexivity.
  Qed.
  


