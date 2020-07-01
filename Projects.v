
Inductive Project : Type :=
| Task : nat -> Project
| Sum : Project -> Project -> Project
| Prod : Project -> Project -> Project
.

Inductive Exec : Project -> Prop :=
| ETask : forall n, Exec (Task n)
| ESumLeft : forall a b, Exec a -> Exec (Sum a b)
| ESumRight : forall a b, Exec b -> Exec (Sum a b)
| EProd : forall a b, Exec a -> Exec b -> Exec (Prod a b)
.

(* Fixpoint execLeft (p : Project) : Exec p := *)
(*   match p with *)
(*   | Task n => ETask n *)
(*   | Sum a b => ESumLeft a b (execLeft a) *)
(*   | Prod a b => EProd a b (execLeft a) (execLeft b) *)
(*   end *)
(*   . *)

(* a is less than b. If b is executed, then a is also executed *)
Definition projLe a b : Prop := Exec b -> Exec a.

Bind Scope project with Project.
Delimit Scope project with proj.
Open Scope project.

Notation "a ':+' b" := (Sum a b) (right associativity, at level 55) : project.

Notation "a ':*' b" := (Prod a b) (right associativity, at level 45) : project.

Notation "a '<=' b" := (projLe a b) (at level 70) : project.

(* Notation "a '>=' b" := (projLe b a) (at level 70) : project. *)

Notation "a '<=>' b" := ((projLe a b) /\ (projLe b a)) (at level 70) : project.

Lemma leTransitive : forall a b c, a <= b -> b <= c -> a <= c.
Proof.
  unfold projLe.
  intros.
  auto.
Qed.

Lemma sumSymmetry : forall a b, a :+ b <=> b :+ a.
Proof.
  unfold projLe.
  split ;
  intros ;
  inversion H ; subst ;
    try (apply ESumRight ; assumption ) ;
    try (apply ESumLeft ; assumption ) .
Qed.

Lemma sumTransitive : forall a b c, a :+ (b :+ c) <= (a :+ b) :+ c .
Proof.
  unfold projLe.
  intros.
  inversion H ; subst. {
    inversion H1 ; subst.
    - apply ESumLeft. assumption.
    - apply ESumRight. apply ESumLeft. assumption.
  } {
    apply ESumRight. apply ESumRight. assumption.
  }
Qed.

Lemma prodSymmetry : forall a b, a :* b <=> b :* a.
Proof.
  unfold projLe.
  split;
    intros ;
    inversion H ; subst;
    constructor ; assumption.
Qed.

Lemma prodTransitive : forall a b c, a :* (b :* c) <=> (a :* b) :* c .
Proof.
  unfold projLe.
  split. {
    intros.
    inversion H ; subst.
    inversion H2 ; subst.
    constructor ; try assumption ; try (constructor ; assumption).
  } {
    intros.
    inversion H ; subst.
    inversion H3 ; subst.
    constructor ; try assumption ; try (constructor ; assumption).
  }
Qed.

Lemma sumDistrib : forall a b c, a :* (b :+ c) <=> a :* b :+ a :* c.
Proof.
  unfold projLe.
  split. {
    intros.
    inversion H ; subst. {
      inversion H1 ; subst.
      - constructor ; try assumption.
        apply ESumLeft. assumption.
    } {
      inversion H1 ; subst.
      constructor ; try assumption.
      apply ESumRight. assumption.
    }
  } {
    intros.
    inversion H ; subst. {
      inversion H3 ; subst. {
        apply ESumLeft. constructor ; assumption.
      } {
        apply ESumRight. constructor ; assumption.
      }
    }
  }
Qed.
