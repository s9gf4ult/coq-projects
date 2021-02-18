Require Import Omega.

Inductive Project : Set :=
| Task : nat -> Project
| Sum : Project -> Project -> Project
| Prod : Project -> Project -> Project
| Seq : Project -> Project -> Project
.

Class is_time time :=
  mk_is_time
    { tle : time -> time -> Prop ; (* Time is less or equal than *)
      tle_refl : forall a, tle a a ;
      tle_transitive : forall a b c, tle a b -> tle b c -> tle a c ;
      tmin : time -> time -> time ; (* Time min *)
      tmin_commut : forall a b, tmin a b = tmin b a ;
      tmax : time -> time -> time ; (* Time max *)
      tmax_commut : forall a b, tmax a b = tmax b a ;
      tle_min_max : forall a b c d, tle a c -> tle b d -> tle (tmin a b) (tmax c d) ;
    }.

Inductive Exec {time : Type} {isTime : is_time time} : Project -> time -> time -> Prop :=
| ETask : forall tid t, Exec (Task tid) t t
| ESumLeft : forall a b lo hi, Exec a lo hi -> Exec (Sum a b) lo hi
| ESumRight : forall a b lo hi, Exec b lo hi -> Exec (Sum a b) lo hi
| EProd : forall a b loA loB hiA hiB,
    Exec a loA hiA ->
    Exec b loB hiB ->
    Exec (Prod a b) (tmin loA loB) (tmax hiA hiB)
| ESeq : forall a b loA loB hiA hiB,
    Exec a loA hiA ->
    Exec b loB hiB ->
    tle hiA loB      ->
    Exec (Seq a b) loA hiB
.



(* a is less than b. If b is executed, then a is also executed *)
Definition projLe {time} {isTime : is_time time} a b :=
  (exists lo1 hi1, @Exec time isTime b lo1 hi1) ->
  (exists lo2 hi2, @Exec time isTime a lo2 hi2).

Definition projGe {time} {isTime : is_time time} a b := projLe b a.

Definition projE {time} {isTime : is_time time} a b :=
  (projLe a b) /\ (projGe a b).

Bind Scope proj_scope with Project.
Delimit Scope proj_scope with proj.
Open Scope proj_scope.

Notation "a ':+' b" := (Sum a b) (right associativity, at level 55) : proj_scope.

Notation "a ':>' b" := (Seq a b) (right associativity, at level 45) : proj_scope.

Notation "a ':*' b" := (Prod a b) (right associativity, at level 35) : proj_scope.

Notation "a '<=' b" := (projLe a b) (at level 70) : proj_scope.

Notation "a '>=' b" := (projGe b a) (at level 70) : proj_scope.

Notation "a '<=>' b" := (projE a b) (at level 70) : proj_scope.

Ltac unfoldproj := unfold projE, projGe, projLe.

Ltac destructexists :=
  repeat match goal with
           H : exists _, _  |- _ => destruct H
         end.

Ltac eexistsall :=
  repeat match goal with
           |- exists _, _ => eexists
         end.

Ltac findExec :=
  match goal with
  | H : Exec ?a _ _ |- Exec ?a _ _ => apply H
  | H : Exec ?a _ _ |- Exec (?a :+ _) _ _ => apply ESumLeft; apply H
  | H : Exec ?a _ _ |- Exec (_ :+ ?a) _ _ => apply ESumRight; apply H
  | H : Exec ?a _ _ |- Exec (_ :+ (?a :+ _)) _ _ => apply ESumRight ; apply ESumLeft; apply H
  | H : Exec ?a _ _ |- Exec (_ :+ (_ :+ ?a)) _ _ => apply ESumRight ; apply ESumRight; apply H
  end.

Ltac applyExEx :=
  lazymatch goal with
  |   Ex: Exec ?a _ _
          , f : ((exists lo1 hi1, Exec ?a lo1 hi1)
                 -> exists lo2 hi2, Exec ?b lo2 hi2)
      |- _
      => assert (exists lo hi, Exec b lo hi)
         ; [ apply f ; eexistsall ; apply Ex | clear f]
  end.



Section Lemmas.
  Context {time : Type}.
  Context {isTime : is_time time}.

  Lemma tle_min : forall a b c, tle a b -> tle (tmin a c) (tmax b c).
  Proof.
    intros.
    apply tle_min_max ; try assumption.
    - apply tle_refl.
  Qed.

  Lemma min_max : forall a b, tle (tmin a b) (tmax a b).
  Proof.
    intros.
    apply tle_min_max ; apply tle_refl.
  Qed.

  Lemma execHiLo : forall a lo hi, Exec a lo hi -> tle lo hi.
  Proof.
    intros.
    induction H ; try assumption. {
      apply tle_refl.
    } {
      apply tle_min_max ; assumption.
    } {
      eapply tle_transitive. {
        eapply tle_transitive.
        - apply IHExec1.
        - apply H1.
      }
      - assumption.
    }
  Qed.

  Lemma projESymmetry : forall a b, a <=> b -> b <=> a.
  Proof.
    unfold projE, projGe, projLe.
    intros.
    inversion H.
    constructor ; assumption.
  Qed.

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
      remember (tmin loB loA) as lo eqn:Le ;
      remember (tmax hiB hiA) as hi eqn:He ;
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

  Fixpoint projEqb (a b : Project) : bool :=
    match a, b with
      | Task x, Task y => Nat.eqb x y
      | Sum x y, Sum u w => projEqb x u && projEqb y w
      | Prod x y, Prod u w => projEqb x u && projEqb y w
      | Seq x y, Seq u w => projEqb x u && projEqb y w
      | _, _ => false
    end.

  Lemma projEqbIsEquivalence : forall a b, projEqb a b = true -> a = b.
  Proof.
    induction a ; intros b H
    ; try (
      destruct b ; try (simpl in H ; congruence ; fail)
    ; simpl in H
    ; symmetry in H
    ; apply Bool.andb_true_eq in H
    ; destruct H as [L R]
    ; symmetry in L, R
    ; apply IHa1 in L
    ; apply IHa2 in R
    ; rewrite L, R
    ; reflexivity
    ; fail ). {
      destruct b ; try (simpl in H ; congruence ; fail). {
        destruct (Nat.eqb n n0) eqn:Neq. {
          apply beq_nat_true in Neq.
          rewrite Neq.
          reflexivity.
        } {
          simpl in H.
          congruence.
        }
      }
    }
  Qed.

  Lemma projEqbRefl : forall a, projEqb a a = true.
  Proof.
    induction a ; intros
    ; try ( simpl ; rewrite IHa1, IHa2 ; reflexivity ; fail ). {
      simpl. apply Nat.eqb_refl.
    }
  Qed.

  Lemma projEqbFalseNeq : forall a b, projEqb a b = false -> a <> b.
  Proof.
    intros a b H.
    intros eq. (* exfalso *)
    rewrite eq in H.
    rewrite projEqbRefl in H.
    discriminate.
  Qed.

  Inductive ProjReplace : Project -> Project -> Project -> Project -> Prop :=
  | ProjRepl : forall orig new, ProjReplace orig orig new new
  | Proj : forall orig a b new,
      (orig <> a) -> PRCase orig a b new -> ProjReplace orig a b new
  with
    PRCase : Project -> Project -> Project -> Project -> Prop :=
  | PRTask : forall n a b, PRCase (Task n) a b (Task n)
  | PRSum : forall p1 p2 p1' p2' a b,
      ProjReplace p1 a b p1'
      -> ProjReplace p2 a b p2'
      -> PRCase (Sum p1 p2) a b (Sum p1' p2')
  | PRProd : forall p1 p2 p1' p2' a b,
      ProjReplace p1 a b p1'
      -> ProjReplace p2 a b p2'
      -> PRCase (Prod p1 p2) a b (Prod p1' p2')
  | PRSeq : forall p1 p2 p1' p2' a b,
      ProjReplace p1 a b p1'
      -> ProjReplace p2 a b p2'
      -> PRCase (Seq p1 p2) a b (Seq p1' p2')
  .

  Lemma ProjReplaceAABB : forall a b, ProjReplace a a b b.
  Proof.
    apply ProjRepl.
  Qed.

  Fixpoint ProjReplaceABBA (a : Project) : forall b, ProjReplace a b b a.
  Proof.
    intros.
    destruct (projEqb a b) eqn:Eq. {
      apply projEqbIsEquivalence in Eq.
      subst.
      apply ProjRepl.
    } {
      apply projEqbFalseNeq in Eq.
      apply Proj ; try assumption.
      destruct a
      ; constructor
      ; repeat (apply ProjReplaceABBA).
    }
  Qed.

  Fixpoint projReplace (orig a b : Project) : Project :=
    match projEqb orig a with
    | true => b
    | false =>
      match orig with
      | Task n => Task n
      | Sum p1 p2 => Sum (projReplace p1 a b) (projReplace p2 a b)
      | Prod p1 p2 => Prod (projReplace p1 a b) (projReplace p2 a b)
      | Seq p1 p2 => Seq (projReplace p1 a b) (projReplace p2 a b)
      end
    end.

  Lemma projReplaceAABB : forall a b, projReplace a a b = b.
  Proof.
    destruct a ; intros
    ; try ( simpl; repeat (rewrite projEqbRefl); simpl; reflexivity ; fail ). {
      simpl. rewrite  Nat.eqb_refl. reflexivity.
    }
  Qed.

  Lemma TaskNeq : forall n1 n2, Task n1 <> Task n2 -> n1 <> n2.
  Proof.
    intros.
    intros eq.
    rewrite eq in H.
    apply H. reflexivity.
  Qed.

  Lemma SumNeqAnd : forall a1 a2 b1 b2, (Sum a1 a2) <> (Sum b1 b2) -> ~ (a1 = b1 /\ a2 = b2).
  Proof.
    intros.
    intros [a b].
    subst.
    apply H.
    reflexivity.
  Qed.

  Lemma SumNeqOr : forall a1 a2 b1 b2, (Sum a1 a2) <> (Sum b1 b2) -> (~ a1 = b1 \/ ~ a2 = b2).
  Proof.
    intros.
    apply SumNeqAnd in H.
    apply Decidable.not_and in H.
    - assumption.
    - unfold Decidable.decidable.
      destruct (projEqb a1 b1) eqn:eq. {
        apply projEqbIsEquivalence in eq.
        left. assumption.
      } {
        apply projEqbFalseNeq in eq.
        right. assumption.
      }
  Qed.

  Lemma ProdNeqAnd : forall a1 a2 b1 b2, (Prod a1 a2) <> (Prod b1 b2) -> ~(a1 = b1 /\ a2 = b2).
  Proof.
    intros.
    intros eq.
    destruct eq.
    subst.
    apply H.
    reflexivity.
  Qed.

  Lemma ProdNeqOr : forall a1 a2 b1 b2, (Prod a1 a2) <> (Prod b1 b2) -> (~ a1 = b1 \/ ~ a2 = b2).
  Proof.
    intros.
    apply ProdNeqAnd in H.
    apply Decidable.not_and in H.
    - assumption.
    - unfold Decidable.decidable.
      destruct (projEqb a1 b1) eqn:eq. {
        apply projEqbIsEquivalence in eq.
        left. assumption.
      } {
        apply projEqbFalseNeq in eq.
        right. assumption.
      }
  Qed.

  Lemma SeqNeqAnd : forall a1 a2 b1 b2, (Seq a1 a2) <> (Seq b1 b2) -> ~(a1 = b1 /\ a2 = b2).
  Proof.
    intros.
    intros eq.
    destruct eq.
    subst.
    apply H.
    reflexivity.
  Qed.

  Lemma SeqNeqOr : forall a1 a2 b1 b2, (Seq a1 a2) <> (Seq b1 b2) -> (~ a1 = b1 \/ ~ a2 = b2).
  Proof.
    intros.
    apply SeqNeqAnd in H.
    apply Decidable.not_and in H.
    - assumption.
    - unfold Decidable.decidable.
      destruct (projEqb a1 b1) eqn:eq. {
        apply projEqbIsEquivalence in eq.
        left. assumption.
      } {
        apply projEqbFalseNeq in eq.
        right. assumption.
      }
  Qed.

  Lemma NeqProjEqbFalse : forall a b, a <> b -> projEqb a b = false.
  Proof.
    induction a ; intros b neq. {
      destruct b ; try (simpl ; reflexivity ; fail). {
        simpl.
        apply TaskNeq in neq.
        apply Nat.eqb_neq. assumption.
      }
    } {
      destruct b ; try (simpl ; reflexivity ; fail). {
        simpl.
        apply SumNeqOr in neq.
        destruct neq. {
          apply IHa1 in H.
          rewrite H.
          reflexivity.
        } {
          apply IHa2 in H.
          rewrite H.
          rewrite Bool.andb_comm.
          reflexivity.
        }
      }
    } {
      destruct b ; try (simpl ; reflexivity ; fail). {
        simpl.
        apply ProdNeqOr in neq.
        destruct neq. {
          apply IHa1 in H.
          rewrite H.
          reflexivity.
        } {
          apply IHa2 in H.
          rewrite H.
          rewrite Bool.andb_comm.
          reflexivity.
        }
      }
    } {
      destruct b ; try (simpl ; reflexivity ; fail). {
        simpl.
        apply SeqNeqOr in neq.
        destruct neq. {
          apply IHa1 in H.
          rewrite H.
          reflexivity.
        } {
          apply IHa2 in H.
          rewrite H.
          rewrite Bool.andb_comm.
          reflexivity.
        }
      }
    }
  Qed.

  Ltac proj_eq_split a b :=
    match goal with
      a : _, b : _ |- _ =>
      destruct (projEqb a b) eqn:eq ;
      [ apply projEqbIsEquivalence in eq
      | apply projEqbFalseNeq in eq ]
    end .

  Fixpoint projReplaceABBA (a b: Project) {struct a}
    : projReplace a b b = a.
  Proof.
    destruct (projEqb a b) eqn:eq. {
      apply projEqbIsEquivalence in eq. subst.
      apply projReplaceAABB.
    } {
      destruct a. {
        destruct b ; try reflexivity. {
          unfold projReplace.
          rewrite eq.
          reflexivity.
        }
      } {
        destruct b ;
          try (
          simpl ;
          repeat (rewrite projReplaceABBA) ;
          reflexivity ;
          fail ).  {
          simpl.
          repeat (rewrite projReplaceABBA).
          apply projEqbFalseNeq in eq.
          apply SumNeqOr in eq.
          destruct eq. {
            apply NeqProjEqbFalse in H.
            rewrite H.
            simpl.
            reflexivity.
          } {
            apply NeqProjEqbFalse in H.
            rewrite H.
            rewrite Bool.andb_comm.
            reflexivity.
          }
        }
      } {
        destruct b ;
          try (
          simpl ;
          repeat (rewrite projReplaceABBA) ;
          reflexivity ;
          fail ).  {
          simpl.
          repeat (rewrite projReplaceABBA).
          apply projEqbFalseNeq in eq.
          apply ProdNeqOr in eq.
          destruct eq. {
            apply NeqProjEqbFalse in H.
            rewrite H.
            simpl.
            reflexivity.
          } {
            apply NeqProjEqbFalse in H.
            rewrite H.
            rewrite Bool.andb_comm.
            reflexivity.
          }
        }
      } {
        destruct b ;
          try (
          simpl ;
          repeat (rewrite projReplaceABBA) ;
          reflexivity ;
          fail ).  {
          simpl.
          repeat (rewrite projReplaceABBA).
          apply projEqbFalseNeq in eq.
          apply SeqNeqOr in eq.
          destruct eq. {
            apply NeqProjEqbFalse in H.
            rewrite H.
            simpl.
            reflexivity.
          } {
            apply NeqProjEqbFalse in H.
            rewrite H.
            rewrite Bool.andb_comm.
            reflexivity.
          }
        }
      }
    }
  Qed.


  Lemma projReplaceToInd (orig : Project) : forall a b new,
      projReplace orig a b = new -> ProjReplace orig a b new.
  Proof.
    intros.
    destruct (projEqb orig a) eqn:Eq. {
      apply projEqbIsEquivalence in Eq. subst.
      rewrite projReplaceAABB.
      apply ProjReplaceAABB.
    } {
      apply projEqbFalseNeq in Eq.
      constructor ; try assumption.
      induction orig. {
        destruct a ; try (simpl in H ; subst ; constructor ; fail). {
          simpl in H.
          apply TaskNeq in Eq.
          rewrite <- Nat.eqb_neq in Eq.
          rewrite Eq in H. subst.
          constructor.
        }
      } {
        destruct a. {
          simpl in H.
          subst.
          constructor. {

          }
          rewrite projReplaceToInd in H.
          assumption.
          constructor.
        }
      }
    }


  Lemma projReplaceNotReversible :
    exists orig a b, orig <> projReplace (projReplace orig a b) b a.
  Proof.
    exists (Task 0), (Task 1), (Task 0).
    intros H.
    simpl in H.
    discriminate.
  Qed.

  Lemma projReplaceReversible :
    forall orig a b, orig <> b -> orig = projReplace (projReplace orig a b) b a.
  Proof.
    induction orig ; intros a b neq. {
      simpl.
      destruct a. {
        remember (n =? n0) as nn0.
        destruct nn0. {
          rewrite projReplaceSameRep.
          apply beq_nat_eq in Heqnn0. rewrite Heqnn0.
          reflexivity.
        } {
          simpl.
          destruct b. {
            remember (n =? n1) as nn1.
            destruct nn1. {

            }

            symmetry in Heqnn0.
            apply beq_nat_false in Heqnn0.

          }

          simpl.
        }
      }
    }


  Lemma replacementPreserves : forall orig a b, a <= b -> (projReplace orig a b) <= orig.
  Proof.
    unfoldproj.
    intros.
    destructexists.



End Lemmas.

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

Instance natIsTime : is_time nat.
Proof.
  eapply mk_is_time. {
    apply le_n.
  } {
    apply Nat.le_trans.
  } {
    apply Nat.min_comm.
  } {
    apply Nat.max_comm.
  } {
    apply minLeMax.
  }
Defined.

Fixpoint execute' (acc : nat) (p : Project) : exists lo hi, (Exec p lo hi /\ (lo > acc)%nat).
Proof.
  destruct p. {
    exists (S acc). eexists.
    split. {
      constructor.
    } {
      auto.
    }
  } {
    destruct (execute' acc p1). destructexists. destruct H.
    eexistsall.
    split. {
      findExec.
    } {
      assumption.
    }
  } {
    destruct (execute' acc p1). destructexists. destruct H.
    destruct (execute' acc p2). destructexists. destruct H1.
    eexistsall.
    split. {
      constructor ; findExec.
    } {
      unfold gt, lt in *.
      apply Nat.min_glb_lt ; assumption.
    }
  } {
    destruct (execute' acc p1). destructexists. destruct H.
    destruct (execute' (S x0) p2). destructexists. destruct H1.
    eexistsall.
    split. {
      eapply ESeq ; try findExec.
      - unfold gt, lt, tle in *.
        simpl in *.
        apply le_Sn_le. apply le_Sn_le. assumption.
    } {
      assumption.
    }
  }
Defined.

(* Any project can be executed at least once *)
Lemma execute : forall p, exists lo hi, (Exec p lo hi).
Proof.
  intros.
  destruct (execute' O p).
  destructexists.
  destruct H.
  eexistsall.
  findExec.
Qed.
