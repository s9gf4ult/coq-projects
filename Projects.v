Require Import Omega.

Inductive Project : Set :=
| Task : nat -> Project
| Sum : Project -> Project -> Project
| Prod : Project -> Project -> Project
| Seq : Project -> Project -> Project
.

Inductive Exec : Project -> nat -> nat -> Prop :=
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
Definition projLe a b : Type := (exists lo1 hi1, Exec b lo1 hi1) -> (exists lo2 hi2, Exec a lo2 hi2).

Definition projGe a b : Type := projLe b a.

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

Open Scope nat.
Lemma minLeMax : forall (a b c d : nat) ,
    a <= c ->
    b <= d ->
    min a b <= max c d.
Proof.
  intros.
  destruct (a <=? b) eqn:AB. {
    apply leb_complete in AB.
    assert (ABmin: min a b = a) by (apply min_l ; assumption).
    rewrite ABmin.
    destruct (c <=? d) eqn:CD. {
      apply leb_complete in CD.
      assert (CDmax : max c d = d) by (apply max_r ; assumption).
      rewrite CDmax.
      omega.
    } {
      rewrite leb_iff_conv in CD.
      assert (CDmax: max c d = c) by (apply max_l ; omega).
      rewrite CDmax.
      omega.
    }
  } {
    apply leb_iff_conv in AB.
    assert (ABmin: min a b = b) by (apply min_r ; omega).
    rewrite ABmin.
    destruct (c <=? d) eqn:CD. {
      apply leb_complete in CD.
      assert (CDmax : max c d = d) by (apply max_r ; assumption).
      rewrite CDmax.
      omega.
    } {
      rewrite leb_iff_conv in CD.
      assert (CDmax: max c d = c) by (apply max_l ; omega).
      rewrite CDmax.
      omega.
    }
  }
Qed.
Close Scope nat.

Lemma execHiLo : forall a lo hi, Exec a hi lo -> (hi <= lo)%nat.
Proof.
  intros.
  induction H ; subst ; try omega.
  - apply minLeMax ; assumption. (* EProd *)
Qed.

Lemma projESymmetry : forall a b, a <=> b -> b <=> a.
Proof.
  unfold projE, projGe, projLe.
  intros.
  inversion H.
  constructor ; assumption.
Qed.

Ltac destructexists :=
  repeat match goal with
           H : exists _, _  |- _ => destruct H
         end.

Ltac eexistsall :=
  repeat match goal with
           |- exists _, _ => eexists
         end.

Ltac unfoldproj := unfold projE, projGe, projLe.

Ltac findExec :=
  match goal with
  | H : Exec ?a _ _ |- Exec ?a _ _ => apply H
  | H : Exec ?a _ _ |- Exec (?a :+ _) _ _ => apply ESumLeft; apply H
  | H : Exec ?a _ _ |- Exec (_ :+ ?a) _ _ => apply ESumRight; apply H
  | H : Exec ?a _ _ |- Exec (_ :+ (?a :+ _)) _ _ => apply ESumRight ; apply ESumLeft; apply H
  | H : Exec ?a _ _ |- Exec (_ :+ (_ :+ ?a)) _ _ => apply ESumRight ; apply ESumRight; apply H
  end.

Lemma leTransitive : forall (a b c : Project), a <= b -> b <= c -> a <= c.
Proof.
  unfoldproj.
  intros.
  auto.
Qed.

Lemma sumSymmetry : forall a b, a :+ b <=> b :+ a.
Proof.
  unfoldproj.
  intros.
  split ; intros ; destructexists ; eexistsall
    ; inversion H ; subst ; findExec.
Qed.

Lemma sumTransitive : forall a b c, a :+ (b :+ c) <= (a :+ b) :+ c .
Proof.
  unfoldproj.
  intros.
  destructexists.
  eexistsall.
  inversion H ; subst. {
    inversion H4 ; subst ; findExec.
  } {
    findExec.
  }
Qed.

Lemma prodSymmetry : forall a b, a :* b <=> b :* a.
Proof.
  unfoldproj.
  intros.
  split ; intros ; destructexists ;
    inversion H ; subst ;
    remember (Init.Nat.min loB loA) as lo eqn:Le ;
    remember (Init.Nat.max hiB hiA) as hi eqn:He ;
    exists lo, hi ;
    rewrite Le;  rewrite He;
     eapply EProd ; assumption.
Qed.

Lemma prodTransitive : forall a b c, a :* (b :* c) <=> (a :* b) :* c .
Proof.
  unfoldproj.
  intros.
  split ; intros ; destructexists ; inversion H ; subst. {
    inversion H2. subst.
    eexistsall.
    constructor ; try findExec ; try constructor ; findExec.
  } {
    inversion H5. subst.
    eexistsall.
    constructor ; try findExec ; try constructor ; findExec.
  }
Qed.

Lemma sumDistrib : forall a b c, a :* (b :+ c) <=> a :* b :+ a :* c.
Proof.
  unfoldproj.
  intros.
  split; intros ; destructexists. {
    inversion H. {
      inversion H4. subst.
      eexistsall.
      constructor ; try findExec; try findExec.
    } {
      inversion H4. subst.
      eexistsall.
      constructor ; try findExec; try findExec.
    }
  } {
    inversion H ; subst.
    inversion H5 ; subst; eexistsall. {
      apply ESumLeft. constructor ; findExec.
    } {
      apply ESumRight. constructor ; findExec.
    }
  }
Qed.

Lemma seqTransitive : forall a b c, a :> (b :> c) <=> (a :> b) :> c.
Proof.
  unfoldproj.
  intros.
  split ; intros; destructexists. {
    inversion H ; subst.
    inversion H2 ; subst.
    eexistsall.
    eapply ESeq.
    - findExec.
    - eapply ESeq ; try findExec ; assumption.
    - assumption.
  } {
    inversion H ; subst.
    inversion H3 ; subst.
    eexistsall.
    eapply ESeq.
    - eapply ESeq; try findExec ; assumption.
    - findExec.
    - assumption.
  }
Qed.

Ltac applyExEx :=
  lazymatch goal with
  |   Ex: Exec ?a _ _
    , f : ((exists lo1 hi1 : nat, Exec ?a lo1 hi1)
           -> exists lo2 hi2 : nat, Exec ?b lo2 hi2)
    |- _
    => assert (exists lo hi : nat, Exec b lo hi) ; [ apply f ; eexistsall ; apply Ex | clear f]
  end.

Lemma prodReduce : forall a b c d ,
    (a <= c) + (a <= d) ->
    (b <= c) + (b <= d) ->
    a :* b <= c :* d.
Proof.
  unfoldproj.
  intros.
  destruct H ; destruct H0 ;
    destructexists ;
    inversion H ; subst ;
    applyExEx ;
    applyExEx ;
    destructexists ;
    eexistsall ;
    constructor ; findExec.
Qed.

Lemma sumReduce : forall a b c d,
    (a <= c) + (b <= c) ->
    (a <= d) + (b <= d) ->
    a :+ b <= c :+ d.
Proof.
  unfoldproj.
  intros.
  destruct H ; destruct H0 ; destructexists ;
    inversion H ; subst;
    applyExEx;
    destructexists;
    eexistsall; findExec.
Qed.
