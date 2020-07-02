Require Import Omega.

Inductive Project : Set :=
| Task : nat -> Project
| Sum : Project -> Project -> Project
| Prod : Project -> Project -> Project
| Seq : Project -> Project -> Project
.

Inductive Exec : Project -> nat -> nat -> Type :=
| ETask : forall (tid ord : nat), Exec (Task tid) ord ord
| ESumLeft : forall a b lo hi, Exec a lo hi -> Exec (Sum a b) lo hi
| ESumRight : forall a b lo hi, Exec b lo hi -> Exec (Sum a b) lo hi
| EProd : forall a b loA loB hiA hiB,
    Exec a loA hiA ->
    Exec b loB hiB ->
    Exec (Prod a b) (min loA loB) (max hiA hiB)
| ESeq : forall a b loA loB hiA hiB,
    Exec a loA hiA ->
    Exec b loB hiB ->
    hiA < loB      ->
    Exec (Seq a b) loA hiB
.

(* a is less than b. If b is executed, then a is also executed *)
Definition projLe a b : Type := forall lo hi, Exec b lo hi -> Exec a lo hi.

Definition projGe a b : Type := forall lo hi, Exec a lo hi -> Exec b lo hi.

Definition projE a b : Type := projLe a b * projGe a b.

Bind Scope proj_scope with Project.
Delimit Scope proj_scope with proj.
Open Scope proj_scope.

Notation "a ':+' b" := (Sum a b) (right associativity, at level 55) : proj_scope.

Notation "a ':>' b" := (Seq a b) (right associativity, at level 45) : proj_scope.

Notation "a ':*' b" := (Prod a b) (right associativity, at level 35) : proj_scope.

Notation "a '<=' b" := (projLe a b) (at level 70) : proj_scope.

Notation "a '>=' b" := (projGe b a) (at level 70) : proj_scope.

Notation "a '<=>' b" := (projE a b) (at level 70) : proj_scope.

Lemma projESymmetry : forall a b, a <=> b -> b <=> a.
Proof.
  unfold projE, projLe, projGe.
  intros.
  inversion H.
  constructor ; assumption.
Qed.

Lemma leTransitive : forall a b c, a <= b -> b <= c -> a <= c.
Proof.
  unfold projLe.
  intros.
  auto.
Qed.

Lemma sumSymmetry : forall a b, a :+ b <=> b :+ a.
Proof.
  unfold projE, projLe, projGe.
  split ;
  intros ;
  inversion H ; subst ;
    try (apply ESumRight ; assumption ) ;
    try (apply ESumLeft ; assumption ) .
Qed.

Lemma sumTransitive : forall a b c, a :+ (b :+ c) <= (a :+ b) :+ c .
Proof.
  unfold projE, projLe, projGe.
  intros.
  inversion H ; subst. {
    inversion H4 ; subst.
    - apply ESumLeft. assumption.
    - apply ESumRight. apply ESumLeft. assumption.
  } {
    apply ESumRight. apply ESumRight. assumption.
  }
Qed.

Lemma prodSymmetry : forall a b, a :* b <=> b :* a.
Proof.
  unfold projE, projLe, projGe.
  intros.
  split;
    intros;
    inversion H;
    rewrite Nat.min_comm;
    rewrite Nat.max_comm;
    constructor ; assumption.
Qed.

Lemma prodTransitive : forall a b c, a :* (b :* c) <=> (a :* b) :* c .
Proof.
  unfold projE, projLe, projGe.
  intros.
  split ; intros ; inversion H. {
    inversion H2. subst a1 b1 loA hiA.
    rewrite <- Nat.min_assoc.
    rewrite <- Nat.max_assoc.
    repeat (constructor ; try assumption).
  } {
    inversion H5. subst a1 b1 loB hiB.
    rewrite Nat.min_assoc.
    rewrite Nat.max_assoc.
    repeat (constructor ; try assumption).
  }
Qed.

Lemma sumDistrib : forall a b c, a :* (b :+ c) <=> a :* b :+ a :* c.
Proof.
  unfold projE, projLe, projGe.
  intros.
  split; intros. {
    inversion H. {
      inversion H4. subst a1 b1 lo hi.
      constructor ; try assumption.
      apply ESumLeft ; assumption.
    } {
      inversion H4. subst a1 b1 lo hi.
      constructor ; try assumption.
      apply ESumRight ; assumption.
    }
  } {
    inversion H ; subst. {
      inversion H5 ; subst. {
        apply ESumLeft. constructor ; assumption.
      } {
        apply ESumRight. constructor ; assumption.
      }
    }
  }
Qed.
