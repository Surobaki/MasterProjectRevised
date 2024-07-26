(* Decidable equality *)
Definition decEq A := forall x y : A, {x = y} + {x <> y}.

Lemma decEqList : forall A, decEq A -> decEq (list A).
Proof.
  unfold decEq. intros A H x y. generalize dependent y.
  induction x as [ | a xs IHy]; intros [ | b ys].
  - left. reflexivity.
  - right. discriminate.
  - right. discriminate.
  - destruct (H a b) as [Hhead | Hhead]; subst.
    + destruct (IHy ys); subst.
      * left. reflexivity.
      * right. intros Hg. inversion Hg. contradiction.
    + destruct (IHy ys); subst.
      * right. intros Hneq. inversion Hneq. contradiction.
      * right. intros Heq. inversion Heq. contradict n. apply H2.
Defined.

Lemma decEqProd : forall A B, decEq A -> decEq B -> decEq (A * B).
Proof.
  unfold decEq. unfold decEq in *.
  intros A B HA HB [x1 x2] [y1 y2].
  destruct (HA x1 y1) as [Heq1 | Heq1];
    destruct (HB x2 y2) as [Heq2 | Heq2].
  - rewrite Heq1. rewrite Heq2. left. reflexivity.
  - right. intros Heqprod.
    apply pair_equal_spec in Heqprod as [Heqleft Heqright].
    subst. contradiction.
  - right. intros Heqprod.
    apply pair_equal_spec in Heqprod as [Heqleft Heqright].
    subst. contradiction.
  - right. intros Heqprod.
    apply pair_equal_spec in Heqprod as [Heqleft Heqright].
    subst. contradiction.
Defined.

Definition decEqNat : decEq nat.
intros ? ?. decide equality.
Defined.

Definition decEqBool : decEq bool.
intros ? ?. decide equality.
Defined.

Require Strings.String.

Definition decEqString : decEq String.string := String.string_dec.
