Require Import Coq.Bool.Bool.
Require Import Lists.List.
Require Import PeanoNat.
Import ListNotations.

Notation "⟨π xy"  := (fst xy) (at level 74, no associativity).
Notation "⟩π xy"  := (snd xy) (at level 74, no associativity).


(**
  Subset of type universe for which properties of a linear order with an
  associated boolean function apply. Requires an ordering function,
  reflexivity, transitivity, antisymmetry and totality.
*)
Record orderedType (X : Type) : Type := mkOrdered
  { ordFunction : X -> X -> bool;
    ordReflexivity : forall (x : X), ordFunction x x = true;
    ordTransitivity : forall (x y z : X), ordFunction x y = true
                                     -> ordFunction y z = true
                                     -> ordFunction x z = true;
    ordAntisymmetry : forall (x y : X), ordFunction x y = true
                                   -> ordFunction y x = true
                                   -> x = y;
    ordTotality : forall (x y : X), ordFunction x y = true \/ ordFunction y x = true
  }.
Arguments ordFunction {X} _ _.
Arguments ordReflexivity {X} _ _.
Arguments ordTransitivity {X} _ _ _ _ _.
Arguments ordAntisymmetry {X} _ _ _ _.
Arguments ordTotality {X} _ _.

Notation "x ⊑? y" := (ordFunction _ x y) (at level 70).
Notation "x ⊑ α ? y" := (ordFunction α x y) (at level 70).


(* Equality in ordered types + lemmas *)

(**
  Helper definition for equality in types inhabiting the [orderedType] record.
  Boolean counterpart of antisymmetry.

  Arguments:
  - [X] - implicit type universe in CoC
  - [O] - linear order requirement
*)
Definition ordEq {X} (O : orderedType X) : X -> X -> bool :=
  fun x y => andb (ordFunction O x y) (ordFunction O y x).
Notation "x =# α # y" := (ordEq α x y) (at level 69, left associativity).

Lemma ordEqReflexivity {X} (O : orderedType X) :
  forall (x : X), x =#O# x = true.
Proof.
  intros x. unfold ordEq. apply Bool.andb_true_iff. split; apply ordReflexivity.
Defined.

Lemma ordEqTransitivity {X} (O : orderedType X) :
  forall (x y z : X), x =#O# y = true -> y =#O# z = true -> x =#O# z = true.
Proof.
  unfold ordEq in *. intros x y z H1 H2.
  apply andb_prop in H1. apply andb_prop in H2.
  destruct H1 as [H11 H12]. destruct H2 as [H21 H22].
  apply Bool.andb_true_iff.
  split.
  - destruct (ordTransitivity O x y z); try split; try auto.
  - destruct (ordTransitivity O z y x); try split; try auto.
Defined.

Lemma ordEq_eq_iff {X} (O : orderedType X) :
  forall (x y : X), x =#O# y = true <-> x = y.
Proof.
  intros x y. split; intros H.
  - unfold ordEq in H. apply andb_prop in H.
    destruct H as [H1 H2]. apply (ordAntisymmetry O x y H1 H2).
  - unfold ordEq. apply andb_true_intro. split;
    unfold ordFunction; rewrite H; apply ordReflexivity.
Defined.

Lemma ordEq_symm_iff {X} (O : orderedType X) :
  forall (x y : X) (b : bool), x =#O# y = b <-> y =#O# x = b.
Proof.
  intros x y b. destruct b; split; intros H;
    unfold ordEq; rewrite Bool.andb_comm; apply H.
Defined.

Lemma ordFun_symm_ordEq {X} (O : orderedType X) :
  forall (x y : X), x ⊑O? y = true -> y ⊑O? x = true -> x =#O# y = true.
Proof.
  intros x y H1 H2. apply Bool.andb_true_iff.
  split. apply H1. apply H2.
Defined.

(* Lexicographically ordered products *)

(**
  Function to lexicographically compare two products with matching
  pairs of [orderedType] linear ordering requirement such that [(x,y)]
  and [(a,b)] can only be compared if [x] and [a] share an order
  as well as [y] and [b] share an ordering.

  Arguments:
  - [X,Y] - implicit type universes in CoC
  - [OX,OY] - linear order requirements for respective type universes
  - [pair1,pair2] - compared pairs such that [pair1 ⊑ pair2] produces a boolean
*)
Definition ordProdFunction {X Y}
  (OX : orderedType X) (OY : orderedType Y) (pair1 pair2 : X * Y) : bool :=
  if (⟨π pair1) =#OX# (⟨π pair2)
    then (⟩π pair1) ⊑OY? (⟩π pair2)
    else (⟨π pair1) ⊑OX? (⟨π pair2).

Notation "x ⊑⟨ γ , ω ⟩? y" := (ordProdFunction γ ω x y) (at level 70).


Lemma ordProdReflexivity {X Y}
  (OX : orderedType X) (OY : orderedType Y) : 
  forall (pair : X * Y), pair ⊑⟨OX,OY⟩? pair = true.
Proof.
  intros pair. unfold ordProdFunction. destruct pair.
  simpl. destruct (x =#OX# x).
  - apply ordReflexivity.
  - apply ordReflexivity.
Defined.

Lemma ordProdTransitivity {X Y} (OX : orderedType X) (OY : orderedType Y) :
  forall (x y z : X * Y), x ⊑⟨OX,OY⟩? y = true -> y ⊑⟨OX,OY⟩? z = true
                   -> x ⊑⟨OX,OY⟩? z = true.
Proof.
  unfold ordProdFunction. intros [x1 x2] [y1 y2] [z1 z2]. simpl.
  intros H1 H2. destruct (x1 =#OX# y1) eqn:Heq1;
    destruct (y1 =#OX# z1) eqn:Heq2; destruct (x1 =#OX# z1) eqn:Heq3;
    try apply ordEq_eq_iff in Heq1; try apply ordEq_eq_iff in Heq2;
    try apply ordEq_eq_iff in Heq3; subst.
  - apply (ordTransitivity _ _ _ _ H1 H2).
  - apply ordReflexivity.
  - rewrite ordEqReflexivity in Heq2. discriminate Heq2.
  - apply H2.
  - rewrite ordEqReflexivity in Heq1. discriminate Heq1.
  - apply H1.
  - assert (Handb : (andb (z1 ⊑OX? y1) (y1 ⊑OX? z1)) = true)
      by exact (ordFun_symm_ordEq _ _ _ H1 H2).
    contradict Handb. apply Bool.not_true_iff_false.
    apply Heq1.
  - unfold ordEq in Heq3. rewrite (ordTransitivity _ _ _ _ H1 H2) in Heq3.
    apply Bool.andb_false_iff in Heq3. destruct Heq3 as [Heq3 | Heq3].
    + discriminate Heq3.
    + apply (ordTransitivity _ _ _ _ H1 H2).
Defined.

Lemma ordProdAntisymmetry {X Y} (OX : orderedType X) (OY : orderedType Y):
  forall (x y : X * Y), x ⊑⟨OX,OY⟩? y = true -> y ⊑⟨OX,OY⟩? x = true -> x = y.
Proof.
  unfold ordProdFunction. intros [x1 x2] [y1 y2]. simpl. intros H1 H2.
  destruct (x1 =#OX# y1) eqn:H3; destruct (y1 =#OX# x1) eqn:H4.
  - assert (Handb : x2 =#OY# y2 = true) by exact (ordFun_symm_ordEq OY _ _ H1 H2).
    apply ordEq_eq_iff in H3. apply ordEq_eq_iff in Handb. subst.
    reflexivity.
  - unfold ordEq in H4. apply Bool.andb_false_iff in H4.
    destruct H4 as [H41 | H42].
    + rewrite H2 in H41. discriminate H41.
    + unfold ordEq in H3. apply Bool.andb_true_iff in H3. destruct H3 as [H31 H32].
      rewrite H42 in H31. discriminate H31.
  - unfold ordEq in H3.
    apply Bool.andb_false_iff in H3. destruct H3 as [H31 | H32].
    + rewrite H1 in H31. discriminate H31.
    + unfold ordEq in H4. apply Bool.andb_true_iff in H4. destruct H4 as [H41 H42].
      rewrite H41 in H32. discriminate H32.
  - apply (ordFun_symm_ordEq _ _ _ H1) in H2.
    rewrite H2 in H3. discriminate H3.
Defined.

Lemma ordProdTotality {X Y} (OX : orderedType X) (OY : orderedType Y):
  forall (x y : X * Y), x ⊑⟨OX,OY⟩? y = true \/ y ⊑⟨OX,OY⟩? x = true.
Proof.
  intros [x1 x2] [y1 y2]. unfold ordProdFunction. simpl.
  destruct (x1 =#OX# y1) eqn:H1; destruct (y1 =#OX# x1) eqn:H2.
  - apply ordTotality.
  - apply ordEq_symm_iff in H1. rewrite H1 in H2. discriminate H2.
  - apply ordEq_symm_iff in H1. rewrite H1 in H2. discriminate H2.
  - apply ordTotality.
Defined.

(**
  Lexicographical ordering over pairs.
*)
Definition lexOrderProd {X Y} (OX : orderedType X) (OY : orderedType Y)
  : orderedType (X * Y) :=
    {|  ordFunction := (ordProdFunction OX OY);
        ordReflexivity := (ordProdReflexivity OX OY);
        ordTransitivity := (ordProdTransitivity OX OY);
        ordAntisymmetry := (ordProdAntisymmetry OX OY);
        ordTotality := (ordProdTotality OX OY)
    |}.


(* Lexicographically ordered lists + lemmas *)

(**
  Function to lexicographically compare two lists under a linear ordering.

  Arguments:
  - [X] - implicit type universe in CoC
  - [O] - linear order requirement
  - [l1,l2] - compared lists such that [l1 ⊑ l2] produces a boolean
*)

Fixpoint ordListFunction {X} (O : orderedType X) (l1 l2 : list X) : bool :=
  match l1 with
  | nil => true

  | h1 :: t1 => match l2 with
              | nil => false
              | h2 :: t2 => andb (h1 ⊑O? h2)
                                     (implb (h2 ⊑O? h1)
                                     (ordListFunction O t1 t2))
                end end.
Notation "x ⊑[ O ]? y" := (ordListFunction O x y) (at level 69).

Lemma ordListReflexivity {X} (O : orderedType X) : forall (l : list X), l ⊑[O]? l = true.
Proof.
  unfold ordListFunction.
  induction l; try reflexivity.
  rewrite (ordReflexivity O a). simpl.
  fold (ordListFunction O l l). fold (ordListFunction O l l) in IHl.
  rewrite IHl.
  reflexivity.
Defined.

Lemma ordListTransitivity {X} (O : orderedType X) : forall (l1 l2 l3 : list X),
    l1 ⊑[O]? l2 = true -> l2 ⊑[O]? l3 = true -> l1 ⊑[O]? l3 = true.
Proof.
  induction l1 as [ | h1 t1 IHl1]; intros l2 l3 H1 H2; try reflexivity.
  destruct l2 as [ | h2 t2] eqn:El2; destruct l3 as [ | h3 t3] eqn:El3.
  - simpl. discriminate.
  - inversion H1.
  - inversion H2.
  - destruct (h1 ⊑O? h3) eqn:Eh13.
    + simpl. rewrite Eh13. destruct (h3 ⊑O? h1) eqn:Eh31; simpl.
      shelve. reflexivity. Unshelve.
      inversion H1 as [H1inv]; inversion H2 as [H2inv].
      (* Mass destruct all relevant boolean checks, throw away nonsense *)
      destruct (h1 ⊑O? h2) eqn:E12; destruct (h2 ⊑O? h3) eqn:E23;
        destruct (h2 ⊑O? h1) eqn:E21; destruct (h3 ⊑O? h2) eqn:E32;
        destruct (t1 ⊑[O]? t2) eqn:Et12; destruct (t2 ⊑[O]? t3) eqn:Et23;
        try discriminate; simpl; simpl in *; subst;
        (* Finish tautologic cases *)
          try assert (IHt13 : t1 ⊑[O]? t3 = true)
           by exact (IHl1 t2 t3 (Et12) (Et23));
          try rewrite IHt13; try reflexivity.
      * specialize (ordAntisymmetry _ _ _ E12 E21) as H3. congruence.
      * specialize (ordAntisymmetry _ _ _ E23 E32) as H3. congruence.
      * specialize (ordAntisymmetry _ _ _ Eh13 Eh31) as H3. congruence.
      * specialize (ordAntisymmetry _ _ _ Eh13 Eh31) as H3. congruence.
      * specialize (ordAntisymmetry _ _ _ Eh13 Eh31) as H3. congruence.
    + simpl in *. rewrite Eh13. simpl. apply andb_prop in H1, H2.
      destruct H1 as [H1l H1r]. destruct H2 as [H2l H2r].
      apply (ordTransitivity _ _ _ _ H1l) in H2l. congruence.
Defined.

Lemma ordListAntisymmetry {X} (O : orderedType X) : forall (l1 l2 : list X),
    l1 ⊑[O]? l2 = true -> l2 ⊑[O]? l1 = true -> l1 = l2.
Proof.
  induction l1 as [ | h1 t1 IH]; destruct l2 as [ | h2 t2]; intros H1 H2;
    simpl in *; try congruence.
  apply andb_prop in H1, H2. destruct H1 as [H1l H1r]. destruct H2 as [H2l H2r].
  apply (Bool.implb_true_iff (h2 ⊑ O ? h1) (t1 ⊑[ O ]? t2)) in H1r; auto.
  apply (Bool.implb_true_iff (h1 ⊑ O ? h2) (t2 ⊑[ O ]? t1)) in H2r; auto.
  specialize (ordAntisymmetry _ _ _ H1l H2l) as H3. subst.
  f_equal. apply IH.
  - apply H1r.
  - apply H2r.
Defined.

Lemma ordListTotality {X} (O : orderedType X) : forall (l1 l2 : list X),
    l1 ⊑[O]? l2 = true \/ l2 ⊑[O]? l1 = true.
Proof.
  induction l1 as [ | h1 t1 IH]; destruct l2 as [ | h2 t2]; try auto.
  destruct (h1 ⊑O? h2) eqn:E12; destruct (h2 ⊑O? h1) eqn:E21; simpl;
    rewrite E12; rewrite E21; simpl.
  - apply IH.
  - left. reflexivity.
  - right. reflexivity.
  - left. destruct (ordTotality O h1 h2); congruence.
Defined.

(**
  Lexicographical ordering over lists.
*)
Definition lexOrderList {X} (O : orderedType X) : orderedType (list X) :=
  {|  ordFunction := (ordListFunction O);
      ordReflexivity := (ordListReflexivity O);
      ordTransitivity := (ordListTransitivity O);
      ordAntisymmetry := (ordListAntisymmetry O);
      ordTotality := (ordListTotality O)
  |}.

Require Import Strings.String.
Open Scope string_scope.

Definition string_compare_refl_eq : forall (s : string), compare s s = Eq.
  induction s as [ | c s' IHs]. reflexivity.
  destruct c as [[|][|][|][|][|][|][|][|]]; try auto.
Defined.

Definition string_leb_reflexive : forall (s : string), leb s s = true.
  induction s as [ | c s' IHs]. reflexivity.
  unfold leb. rewrite (string_compare_refl_eq (String c s')). reflexivity.
Defined.

Definition string_compare_trans_eq : forall (s1 s2 s3 : string),
    compare s1 s2 = Eq -> compare s2 s3 = Eq -> compare s1 s3 = Eq.
  intros. apply compare_eq_iff in H. apply compare_eq_iff in H0.
  subst. apply string_compare_refl_eq.
Defined.

Definition asciiCompareEq : forall a, Ascii.compare a a = Eq.
  intros.
  destruct (Ascii.compare a a) eqn:H; assert (H' := H); auto;
  rewrite Ascii.compare_antisym, H in H'; simpl in *; exfalso; congruence.
Defined.

Definition string_leb_cons : forall s1 s2, forall a1 a2,
  String a1 s1 <=? String a2 s2 = true <->
    a1 = a2 /\ s1 <=? s2 = true \/ Ascii.compare a1 a2 = Lt.
 unfold leb; simpl.
 intros ? ? ? ?; destruct (Ascii.compare a1 a2) eqn:Ea; auto.
 + apply Ascii.compare_eq_iff in Ea; subst.
   split; eauto.
   intros [[_ ?]|]; eauto.
   inversion H.
 + split; auto.
 + split; [intros e; inversion e |].
   intros [[? _]|e]; [|inversion e].
   subst.
   rewrite asciiCompareEq in Ea; inversion Ea.
Defined.

Axiom asciiCompareTransLt :
  forall a b c, Ascii.compare a b = Lt
           -> Ascii.compare b c = Lt
           -> Ascii.compare a c = Lt.

Definition string_leb_transitive : forall (s1 s2 s3 : string),
    leb s1 s2 = true -> leb s2 s3 = true -> leb s1 s3 = true.
  intros s1 s2; revert s1; induction s2.
  + intros s1 s3 H _; destruct s1; inversion H; destruct s3; reflexivity.
  + intros s1; destruct s1; [intros [|] _ _; reflexivity |].
    simpl; intros.
    destruct s3; [inversion H0|].
    apply string_leb_cons in H, H0.
    apply string_leb_cons.
    destruct H as [[? H]|H];
    destruct H0 as [[? H0]|H0]; subst; eauto.
    right; eapply asciiCompareTransLt; eauto.
Defined.

Definition lexOrderString : orderedType string :=
  {| ordFunction := leb;
     ordReflexivity := string_leb_reflexive;
     ordTransitivity := string_leb_transitive;
     ordAntisymmetry := leb_antisym;
     ordTotality := leb_total
  |}.


Definition natOrdFun := Nat.leb.
Definition natOrdRefl := Nat.leb_refl.
Definition natOrdTrans : forall x y z, Nat.leb x y = true -> Nat.leb y z = true
                                  -> Nat.leb x z = true.
intros x y z H1 H2.
apply Nat.leb_le in H1. apply Nat.leb_le in H2. apply Nat.leb_le.
transitivity y. apply H1. apply H2. Defined.
Definition natOrdAntis : forall x y, Nat.leb x y = true -> Nat.leb y x = true -> x = y.
intros x y H1 H2. apply Nat.leb_le in H1. apply Nat.leb_le in H2.
apply (Nat.le_antisymm x y H1 H2).
Defined.
Definition natOrdTot : forall x y, Nat.leb x y = true \/ Nat.leb y x = true.
intros x. induction x; intros y.
- left. apply Nat.leb_le. apply le_0_n.
- rewrite Nat.leb_le. rewrite Nat.leb_le. apply Nat.le_ge_cases.
Defined.

Definition lexOrderNat : orderedType nat :=
  {| ordFunction := natOrdFun;
     ordReflexivity := natOrdRefl;
     ordTransitivity := natOrdTrans;
     ordAntisymmetry := natOrdAntis;
     ordTotality := natOrdTot
  |}.

Definition boolOrdFun (x y : bool) :=
match x with
| false => true
| true => y
end.
Definition boolOrdRefl : forall x, boolOrdFun x x = true.
intros [|]; auto. Defined.
Definition boolOrdTrans : forall x y z, boolOrdFun x y = true -> boolOrdFun y z = true
                                   -> boolOrdFun x z = true.
intros [|] [|] [|]; auto. Defined.
Definition boolOrdAntisym : forall x y, boolOrdFun x y = true -> boolOrdFun y x = true
                                 -> x = y.
intros [|] [|]; auto. Defined.
Definition boolOrdTotal : forall x y, boolOrdFun x y = true \/ boolOrdFun y x = true.
intros [|] [|]; auto. Defined.

Definition lexOrderBool : orderedType bool :=
  {| ordFunction := boolOrdFun;
     ordReflexivity := boolOrdRefl;
     ordTransitivity := boolOrdTrans;
     ordAntisymmetry := boolOrdAntisym;
     ordTotality := boolOrdTotal
  |}.
