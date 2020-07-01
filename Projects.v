
Inductive Project : Type :=
| Task : nat -> Project
| Sum : Project -> Project -> Project
| Prod : Project -> Project -> Project
.

Notation "a '+' b" := (Sum a b).

Notation "a '*' b" := (Prod a b).

Inductive Exec : Project -> Prop :=
| ETask : forall n, Exec (Task n)
| ESumLeft : forall a b, Exec a -> Exec (Sum a b)
| ESumRight : forall a b, Exec b -> Exec (Sum a b)
| EProd : forall a b, Exec a -> Exec b -> Exec (Prod a b)
.

(* a is less than b. If b is executed, then a is also executed *)
Definition projLe a b : Prop := Exec b -> Exec a.

Notation "a '<=' b" := (projLe a b).

Lemma leTransitive : forall a b c, a <= b -> b <= c -> a <= c.
Proof.
  unfold projLe.
  intros.
  auto.
Qed.

Lemma sumSymmetry : forall a b, a + b <= b + a.
Proof.
  unfold projLe.
  intros.
  inversion H ; subst.
  - apply ESumRight. assumption.
  - apply ESumLeft. assumption.
Qed.

Lemma prodSymmetry : forall a b, a * b <= b * a.
Proof.
  unfold projLe.
  intros.
  inversion H ; subst.
  constructor ; assumption.
Qed.
