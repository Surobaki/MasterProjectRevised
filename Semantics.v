Require Import List.
Require Import PropExtensionality.
Require Import FunctionalExtensionality.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
From NRCFormalisation Require Import Syntax.
From NRCFormalisation Require Import DecidableEquality.
From NRCFormalisation Require Import OrderedTypes.

Declare Scope sort_scope.
Bind Scope sort_scope with sort.

(* Basic notations *)
Notation "'1'"   := sort_unit : sort_scope.
Notation "'ι'"   := sort_atom : sort_scope.
Notation "'β'"   := sort_pow : sort_scope.
Notation "τ × σ" := (sort_prod τ σ) (at level 62) : sort_scope.
Notation "^ X"   := (option X) (at level 5) : type_scope.
Notation "θ & A" := (@option_rect _ (fun _ => _) θ A) (at level 41).
Notation "⟨π xy"  := (fst xy) (at level 74, no associativity).
Notation "⟩π xy"  := (snd xy) (at level 74, no associativity).


(* Use Section to instantiate functions with a CoC Type lambda later. *)
Section Sem.

(* Interpretation variables to ensure type universe consistency over section *)
Variable U : Type.
Variable UDecEq : decEq U.
Variable Uord : orderedType U.

Open Scope sort_scope.

(**
  A type interpretation function to produce simple
  Prop-based semantics in the universe of CoC.  

  Arguments:  
  - [τ] - a type from within the universe of Nested Relational Calculus.
*)
Fixpoint interpSortProp (τ : sort) : Type :=
  match τ with
  | ι t => interpBase t
  | 1 => unit
  | τ × σ => interpSortProp τ * interpSortProp σ
  | β τ => interpSortProp τ -> Prop
  end.

(**
  An interpretation function transferring a contextful syntactic term
  from Nested Relational Calculus (NRC) into a Prop-based interpretation
  of NRC types.

  Arguments:
  - [X] - implicit background CoC type universe
  - [Σ] - syntactic context as a function from CoC types to NRC sorts
  - [τ] - implicit NRC sort used in syntactic term
  - [t] - provided NRC syntax term
  - [ρ] - hypothesis giving standard interpretation to all CoC types in NRC
    universe
*)
Fixpoint interpStxProp {X} {Σ : X -> _} {τ} (t : nrc__stx Σ τ)
  (ρ : forall x, interpSortProp (Σ x)) : interpSortProp τ :=
  match t with
    nrc_var _ x => ρ x
  | nrc_pair _ _ _ t u => (interpStxProp t ρ, interpStxProp u ρ)
  | nrc_proj1 _ _ _ t => ⟨π interpStxProp t ρ
  | nrc_proj2 _ _ _ t => ⟩π interpStxProp t ρ
  | nrc_unit _ => tt
  | nrc_empty _ _ => fun _ => False
  | nrc_sing _ _ t => fun z => z = interpStxProp t ρ
  | nrc_cup _ _ t u => fun z => interpStxProp t ρ z \/ interpStxProp u ρ z
  | nrc_bigcup _ _ _ t u => fun z => exists y, interpStxProp t ρ y /\
                                      interpStxProp u (ρ & y) z
  | nrc_diff _ _ t u => fun z => interpStxProp t ρ z /\ (~ interpStxProp u ρ z)
  end.

(**
  A type interpretation function to produce effective list semantics
  of Nested Relational Calculus (NRC) types in the universe of CoC.

  Arguments:
  - [τ] - a type from within the universe of Nested Relational Calculus.
*)
Fixpoint interpSortEff (τ : sort) : Type :=
  match τ with
  | ι t => interpBase t
  | 1 => unit
  | τ × σ => interpSortEff τ * interpSortEff σ
  | β τ => list (interpSortEff τ)
  end.

Definition decEqInterpSortEff (τ : sort) : decEq (interpSortEff τ).
unfold decEq in *. intros x y. 
induction τ.
- simpl in *. destruct b. apply decEqNat. apply decEqString. apply decEqBool. 
- destruct x. destruct y. auto.
- apply decEqList in IHτ. apply IHτ.
- destruct x as [x1 x2]. destruct y as [y1 y2].
  apply (decEqProd (interpSortEff τ1) (interpSortEff τ2)); unfold decEq.
  + apply IHτ1.
  + apply IHτ2.
Defined.

(* TODO: Move out of section, perhaps different file if cohesive *)
(**
  Function over types with decidable equality to remove all occurrences
  of a single element in a homogenous list.

  Arguments:
  - [X] - implicit type universe in CoC
  - [D] - decidable equality requirement
  - [e] - element to be removed
  - [A] - list to remove element from
*)
Definition removeAll {X : Type} (D : decEq X) (e : X) (A : list X) : list X :=
  filter (fun x => match (D e x) with
                | left _ => false
                | right _ => true end) A.

(* TODO: Move out of section, perhaps different file if cohesive *)
Lemma removeAll_in {X : Type} {D A} {e : X} : forall x, In x (removeAll D e A)
  <-> x <> e /\ In x A.
  intros.
  split; intros.
  + apply filter_In in H.
    destruct H, (D e x); try  discriminate; eauto.
  + apply filter_In;
    destruct H, (D e x); try  discriminate; eauto.
Qed.

(* TODO: Move out of section, perhaps different file if cohesive *)
(**
  Function to subtract one list from another with set-like subtraction behaviour.

  Arguments:
  - [X] - implicit type universe in CoC
  - [D] - decidable equality requirement
  - [A] - left term of subtraction (minuend)
  - [B] - right term of subtraction (subtrahend)
*)
Fixpoint listSubtr {X : Type} (D : decEq X) (A B : list X) : list X :=
  match B with
    nil => A
  | x :: B' => removeAll D x (listSubtr D A B')
  end.

(* TODO: Move out of section, perhaps different file if cohesive *)
Lemma listSubtr_in {X : Type} {D} {A B : list X} : forall x, In x (listSubtr D A B)
  <-> In x A /\ ~ In x B.
  induction B; intros; simpl in *; try tauto.
  split; intros.
  + apply removeAll_in in H.
    destruct H as [H1 H2]; apply IHB in H2.
    destruct H2; split; auto.
    intros [|].
    - rewrite H2 in H1; apply H1; reflexivity.
    -  auto.
  + apply removeAll_in.
    destruct H; split; eauto.
    apply IHB; split; eauto.
  Qed.

Definition unit_ordFunction : unit -> unit -> bool :=
  fun u _ => match u with tt => true end.

Definition unit_ordReflexivity : forall (x : unit), unit_ordFunction x x = true.
Proof.
  intros []. reflexivity.
Defined.

Definition unit_ordTransitivity :
  forall (x y z : unit), unit_ordFunction x y = true ->
                    unit_ordFunction y z = true ->
                    unit_ordFunction x z = true.
Proof.
  intros [] [] []. auto.
Defined.

Definition unit_ordAntisymmetry :
  forall (x y : unit), unit_ordFunction x y = true ->
                  unit_ordFunction y x = true ->
                  x = y.
Proof.
  intros [] []. auto.
Defined.

Definition unit_ordTotality :
  forall (x y : unit), unit_ordFunction x y = true \/ unit_ordFunction y x = true.
Proof.
  intros [] []. left. reflexivity.
Defined.

Definition ordUnit : orderedType unit :=
    {|  ordFunction := unit_ordFunction;
        ordReflexivity := unit_ordReflexivity;
        ordTransitivity := unit_ordTransitivity;
        ordAntisymmetry := unit_ordAntisymmetry;
        ordTotality := unit_ordTotality
    |}.

(**
  Lexicographical ordering over effective list semantics of
  Nested Relational Calculus universe types.
*)
Definition lexOrderInterpSortEff : forall τ, orderedType (interpSortEff τ).
  induction τ as [ |  | τ IH | τ IHl σ IHr]; simpl.
  - destruct b; simpl.
    + apply lexOrderNat.
    + apply lexOrderString.
    + apply lexOrderBool.
  - apply ordUnit.
  - apply (lexOrderList IH).
  - apply (lexOrderProd IHl IHr).
Defined.

(* TODO: Move out of section, perhaps different file if cohesive *)
Lemma ordDecEq {X : Type} (O : orderedType X) : decEq X.
Proof using Type.
  unfold decEq. intros x y. destruct O.
  case_eq (ordFunction x y); case_eq (ordFunction y x); intros H1 H2.
  - left. apply ordAntisymmetry. apply H2. apply H1.
  - right. intros Hnot. subst. rewrite H2 in H1. inversion H1.
  - right. intros Hnot. subst. rewrite H2 in H1. inversion H1.
  - right. intros Hnot. subst. rewrite ordReflexivity in H1. inversion H1.
Defined.

(* TODO: Move out of section, perhaps different file if cohesive *)
(**
  Function to insert n element into a list with respect to a linear order.

  Arguments:
  - [X] - implicit type universe in CoC
  - [O] - linear order requirement
  - [e] - element to insert into the list [l]
  - [l] - list into which the element [e] is inserted
*)
Fixpoint insert {X : Type} (O : orderedType X) (e : X) (l : list X) : list X :=
  match l with
  | nil => e :: nil
  | x :: xs => if ordFunction O e x then e :: l else x :: insert O e xs
  end.

(* TODO: Move out of section, perhaps different file if cohesive *)
Lemma insert_member {X : Type} (O : orderedType X) (e : X) (l : list X) :
  forall (x : X), In x (insert O e l) <-> In x l \/ x = e.
Proof.
  induction l; intros x; split; intros H.
  - destruct H.
    + subst. right. reflexivity.
    + left. apply H.
  - destruct H as [H | H].
    + simpl. destruct H.
    + subst. simpl. left. reflexivity.
  - simpl in H. simpl. destruct (e ⊑O? a) eqn:E; simpl in H.
    + destruct H as [H | H].
      * subst. right. reflexivity.
      * left. apply H.
    + destruct H as [H | H].
      * left. left. apply H.
      * apply IHl in H. destruct H as [H | H].
        -- left. right. apply H.
        -- right. apply H.
  - simpl. destruct (e ⊑O? a) eqn:E. 
    + simpl in *. destruct H as [[? | ?] | ?]; subst; auto. 
    + simpl in *. destruct H as [[? | ?] | ?]; subst;
       (right; apply IHl; auto; fail) ||  left; auto. 
Defined.
      
(* TODO: Move out of section, perhaps different file if cohesive *)
(**
  Function to sort a list according to a linear order
  by reinserting every element. High computational complexity.

  Arguments:
  - [X] - implicit type universe in CoC
  - [O] - linear order requirement
  - [l] - list to sort
*)
Fixpoint insertSort {X : Type} (O : orderedType X) (l : list X) : list X :=
  match l with
  | nil => nil
  | x :: xs => insert O x (insertSort O xs)
  end.

(* TODO: Move out of section, perhaps different file if cohesive *)
(**
  Inductive version of general sorted lists for use in proofs.

  Arguments:
  - [X] - implicit type universe in CoC
  - [O] - linear order requirement
**)
Inductive Sorted {X : Type} (O : orderedType X) : list X -> Prop :=
  | Sorted_nil : Sorted O nil
  | Sorted_cons (x : X) (xs : list X)
      (H_prev : Sorted O xs)
      (H_app : forall (y : X), In y xs -> x ⊑O? y = true)
    : Sorted O (x :: xs).

(* TODO: Move out of section, perhaps different file if cohesive *)
Lemma insertSort_member {X : Type} (O : orderedType X) (l : list X) :
  forall (x : X), In x l <-> In x (insertSort O l).
Proof.
  induction l; intros x; split; intros H; try destruct H.
  - subst. simpl. apply insert_member. right. reflexivity.
  - simpl. apply insert_member. left. apply IHl. apply H.
  - simpl in H. apply insert_member in H. destruct H as [H | H].
    + apply IHl in H. simpl. right. apply H.
    + subst. simpl. left. reflexivity.
Defined.

(* TODO: Move out of section, perhaps different file if cohesive *)
(**
  Conversion lemma between computational insertSort (in Prop-form)
  and a Sorted expression.

  Arguments:
  - [X] - implicit type universe in CoC
  - [O] - linear order requirement
  - [l] - sorted list
**)
Lemma insertSort_fixed_point {X : Type} (O : orderedType X) (l : list X) :
  Sorted O l -> insertSort O l = l.
Proof.
  induction l as [ | h t IH_l]; intros H.
  - reflexivity.
  - simpl. inversion H. subst. rewrite IH_l; auto.
    clear IH_l H. destruct t.
    + reflexivity.
    + simpl. specialize (H_app x). specialize (H_app (in_eq x t)).
      rewrite H_app. reflexivity.
Defined.

(* TODO: Move out of section, perhaps different file if cohesive *)
(**
  Lemma weakening Sorted_cons constructor for the insert operation.

  Arguments:
  - [X] - implicit type universe in CoC
  - [O] - linear order requirement

  Quantified variables:
  - [x : X] - element to be inserted and sorted
  - [xs : list X] - original list of sorted elements
**)
Lemma Sorted_invariant {X : Type} (O : orderedType X) :
  forall (x : X) (xs : list X),
    Sorted O xs -> Sorted O (insert O x xs).
Proof.
  induction xs as [ | h t IH_xs]; intros H; simpl.
  - constructor; auto.
  - inversion H. subst. specialize (IH_xs H_prev).
    (* Is x before or after h in list? *)
    destruct (x ⊑O? h) eqn:E.
    + apply Sorted_cons. apply H. intros y H_in. specialize (H_app y).
      destruct H_in. subst. apply E. specialize (H_app H0).
      apply (ordTransitivity O x h y E). apply H_app.
    + apply Sorted_cons. apply IH_xs. intros y H_in.
      apply insert_member in H_in. destruct H_in.
      * specialize (H_app _ H0). apply H_app.
      * subst. assert (H_tot := ordTotality O x h).
        destruct H_tot; auto. rewrite E in H0. discriminate H0.
Defined.
        
(* TODO: Move out of section, perhaps different file if cohesive *)
(**
  Lemma qualifying insertSort as a form of Sorted type.

  Arguments:
  - [X] - implicit type universe in CoC
  - [O] - linear order requirement
  - [l] - sorted list
**)
Lemma Sorted_insertSort {X : Type} (O : orderedType X) (l : list X) :
  Sorted O (insertSort O l).
Proof.
  induction l as [ | h t IHl].
  - simpl. apply Sorted_nil.
  - simpl. apply Sorted_invariant. apply IHl.
Defined.

(* TODO: Move out of section, perhaps different file if cohesive *)
(**
  Function to normalise a list with a linear order by removing duplicates and
  performing a sort.

  Arguments:
  - [X] - implicit type universe in CoC
  - [O] - linear order requirement
  - [l] - list to normalise
*)
Definition normaliseListRepr {X : Type} (O : orderedType X) (l : list X) : list X :=
  insertSort O (nodup (ordDecEq O) l).

(* TODO: Move out of section, perhaps different file if cohesive *)
(**
  Lemma stating membership irrelevance over normalised vs unnormalised lists.

  Arguments:
  - [X] - implicit type universe in CoC
  - [O] - linear order requirement

  Quantified variables:
  - [x : X] - arbitrary element of xs
  - [xs : list X] - either a normalised or unnormalised list
**)
Lemma normaliseList_member {X : Type} (O : orderedType X) :
  forall (x : X) (l : list X), In x l <-> In x (normaliseListRepr O l).
Proof.
  unfold normaliseListRepr. intros x; split; intros H.
  - apply insertSort_member. apply nodup_In. apply H.
  - apply insertSort_member in H. apply nodup_In in H. apply H.
Defined.

(*
These definitions are an artifact of the development process. After switch to
inductive forms of insertSort, nodup and normaliseListRepr they are no longer necessary.

Definition noDupList {X : Type} (O : orderedType X) (xs : list X) :=
  nodup (ordDecEq O) xs = xs.

Definition sortedList {X : Type} (O : orderedType X) (xs : list X) :=
  insertSort O xs = xs.

Definition normalList {X : Type} (O : orderedType X) (xs : list X) :=
  normaliseListRepr O xs = xs.
*)

(**
  Lemma showing idempotency of computational insertSort.

  Arguments:
  - [X] - implicit type universe in CoC
  - [O] - linear order requirement

  Quantified variables:
  - [xs : list X] - arbitrary sorted list
**)
Lemma insertSort_idem {X : Type} (O : orderedType X) :
  forall (xs : list X),
    insertSort O (insertSort O xs) = insertSort O xs.
Proof.
  destruct xs as [ | h t].
  - reflexivity.
  - simpl. apply insertSort_fixed_point.
    apply Sorted_invariant. apply Sorted_insertSort.
Defined.

(**
  Lemma showing computational normalisation as a consequence of
  inductively sorted and inductively deduplicated lists.

  Arguments:
  - [X] - implicit type universe in CoC
  - [O] - linear order requirement
  - [xs] - subject list
**)
Lemma normalList_Sorted_NoDup {X : Type} (O : orderedType X) (xs : list X) :
  Sorted O xs -> NoDup xs -> normaliseListRepr O xs = xs.
Proof.
  intros H_sort H_dup. unfold normaliseListRepr. rewrite nodup_fixed_point.
  - apply insertSort_fixed_point. apply H_sort.
  - apply H_dup.
Defined.

(**
  Lemma showing preservation of NoDup over unique inserted element.

  Arguments:
  - [X] - implicit type universe in CoC
  - [O] - linear order requirement

  Quantified variables:
  - [x : X] - unique inserted element
  - [xs : list X] - subject list
**)
Lemma insert_NoDup_preserv {X : Type} (O : orderedType X) :
  forall (x : X) (xs : list X),
    ~ In x xs -> NoDup xs -> NoDup (insert O x xs).
Proof.
  intros x xs H_nin H_dup. induction xs as [ | h t IH_xs]; simpl.
  - constructor; auto.
  - destruct (x ⊑O? h) eqn:E.
    + apply NoDup_cons. apply H_nin. apply H_dup.
    + apply NoDup_cons.
      * intro H.
        apply insert_member in H.
        apply H_nin; simpl; destruct H; auto.
        inversion H_dup; subst; contradiction.
      * inversion H_dup; subst.
        apply IH_xs; auto.
        intro H; apply H_nin.
        simpl; auto.
Qed.

Lemma listSubtr_nil {X : Type} D :
  forall (xs : list X), listSubtr D nil xs = nil.
Proof.
  intros; apply incl_l_nil.
  intros ? ?.
  apply listSubtr_in in H; destruct H; auto.
Qed.

Lemma removeAll_NoDup {X : Type} D :
  forall xs, NoDup xs ->
        forall x : X, NoDup (removeAll D x xs).
Proof.
  intros xs ND; induction ND; simpl in *; intros; try constructor.
  destruct (D x0 x); [|constructor]; auto.
  intro H'; apply removeAll_in in H'; destruct H'; contradiction.
Qed.

Lemma listSubtr_NoDup {X : Type} D :
  forall (ys xs : list X),
    NoDup xs -> NoDup (listSubtr D xs ys).
Proof.
  induction ys; intros xs ND; simpl in *; auto.
  apply removeAll_NoDup; auto.
Qed.

Lemma removeAll_Sorted {X : Type} O D :
  forall xs, Sorted O xs ->
        forall x : X, Sorted O (removeAll D x xs).
Proof.
  intros xs ND; induction ND; simpl in *; intros; try constructor.
  destruct (D x0 x); [|constructor]; auto.
  intros ? H'; apply removeAll_in in H'; destruct H'; auto.
Qed.

Lemma listSubtr_Sorted {X : Type} O D :
  forall (ys xs : list X),
    Sorted O xs -> Sorted O (listSubtr D xs ys).
Proof.
  induction ys; intros xs ND; simpl in *; auto.
  apply removeAll_Sorted; auto.
Qed.

(**
  Lemma showing that insertSort preserves NoDup property.

  Arguments:
  - [X] - implicit type universe in CoC
  - [O] - linear order requirement

  Quantified variables:
  - [xs : list X] - list over which insertSort is performed
**)
Lemma insertSort_nodup_preserv {X : Type} (O : orderedType X) :
  forall (xs : list X), NoDup xs -> NoDup (insertSort O xs).
Proof.
  intros xs H. induction xs as [ | h t IH_xs]; simpl.
  - apply NoDup_nil.
  - apply insert_NoDup_preserv.
    + intro H'; apply insertSort_member in H'.
      inversion H; subst; auto.
    + apply IH_xs; inversion H; subst; auto. 
Qed.

(**
  Lemma showing that computational normalisation is idempotent.

  Arguments:
  - [X] - implicit type universe in CoC
  - [O] - linear order requirement
**)
Lemma normalList_idem {X : Type} (O : orderedType X) :
  forall (xs : list X), normaliseListRepr O (normaliseListRepr O xs) = normaliseListRepr O xs.
Proof.
  intros xs. apply normalList_Sorted_NoDup.
  - unfold normaliseListRepr. apply Sorted_insertSort.
  - unfold normaliseListRepr. apply insertSort_nodup_preserv.
    apply NoDup_nodup.
Qed.

(* Lemma normalListRepr {X : Type} (O : orderedType X) :
  forall xs ys, (forall x, In x xs <-> In x ys) ->
           normalList O xs -> normalList O ys ->
           xs = ys. *)

(**
  Function to normalise a type interpretation of Nested Relational Calculus (NRC)
  effective list semantics via list normalisation.

  Arguments:
  - [τ] - NRC sort used in semantic interpretation
  - [x] - interpreted NRC term designated for normalisation
*)
Fixpoint normaliseInterpSortEff {τ} (x : interpSortEff τ) : interpSortEff τ :=
  match τ return interpSortEff τ -> interpSortEff τ with
  | ι t => fun x => x
  | 1 => fun x => tt
  | β σ => fun x => normaliseListRepr (lexOrderInterpSortEff σ) (map normaliseInterpSortEff x)
  | τ × σ => fun x => let (y,z) := x in (normaliseInterpSortEff y, normaliseInterpSortEff z)
  end x.

(* TODO: Remove *)
Lemma normaliseInterpSortEff_idem {τ} (x : interpSortEff τ) :
  normaliseInterpSortEff (normaliseInterpSortEff x) = normaliseInterpSortEff x.
Proof.
  induction τ as [ | | τ' IHτ | σ τ IHτ].
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl in x. simpl. (* Here it would be ideal to conver normaliseInterpSortEff
                          to an inductively defined version. *)
Admitted.

(* I believe this definition should be deprecated for the inductive version.
   Below is a version that is defined as a Fixpoint with the convoy pattern. *)
(*
Definition normal {τ} (x : interpSortEff τ) := normaliseInterpSortEff x = x.
*)

(**
  A function interpreting a syntactic Nested Relational Calculus (NRC) term
  in effective list semantics.

  Arguments:
  - [X] - implicit background CoC type universe
  - [Σ] - syntactic context as a function from CoC types to NRC sorts
  - [τ] - implicit NRC sort used in syntactic term
  - [t] - provided NRC syntax term
  - [ρ] - hypothesis giving standard interpretation to all CoC types in NRC universe
*)
Fixpoint interpStxEff {X} {Σ : X -> _} {τ} (t : nrc__stx Σ τ)
  (ρ : forall x, interpSortEff (Σ x)): interpSortEff τ :=
  match t with
    nrc_var _ x => normaliseInterpSortEff (ρ x)
  | nrc_pair _ _ _ t u => ((interpStxEff t ρ), (interpStxEff u ρ))
  | nrc_proj1 _ _ _ t => fst (interpStxEff t ρ)
  | nrc_proj2 _ _ _ t => snd (interpStxEff t ρ)
  | nrc_empty _ _ => nil
  | nrc_unit _ => tt
  | nrc_sing _ _ t => (interpStxEff t ρ :: nil)
  | nrc_cup _ _ t u => normaliseListRepr (lexOrderInterpSortEff _)
                        (interpStxEff t ρ ++ interpStxEff u ρ)
  | nrc_bigcup _ _ _ t u => normaliseListRepr (lexOrderInterpSortEff _)
                             (concat (map (fun x => interpStxEff u (ρ & x)) (interpStxEff t ρ)))
  | nrc_diff _ _ t u => listSubtr (decEqInterpSortEff _) (interpStxEff t ρ) (interpStxEff u ρ)
  end.

(* At this point you can run a computation over NRC! To see it, skip the
    following sections and just put in an `End Sem.` directive, then use
    the `Compute interpStxEff nat example listUpTo.` directive. *)

(* Below is a theorem about relating the two interpretation functions for
    syntax defined above. *)

(* First, we define an embedding of the domain interpreting sets using
    lists to the domain using Prop. *)
Fixpoint eff2Prop {τ : sort} : interpSortEff τ -> interpSortProp τ :=
  match τ return interpSortEff τ -> interpSortProp τ with
    ι t => fun x => x
  | 1 => fun x => tt
  | τ × σ => fun x =>
      let (x1, x2) := x in
      (eff2Prop x1, eff2Prop x2)
  | β τ => fun xs y => In y (map eff2Prop xs)
  end.

Notation "f ∘ g" := (fun x => f (g x)) (at level 67, left associativity).

Definition injective {A B : Type} (f : A -> B) := forall x y, f x = f y -> x = y.

Definition listMemEqv {A : Type} (xs ys : list A) := forall x, In x xs <-> In x ys.

Definition listIncl {A : Type} (xs ys : list A) := forall x, In x xs -> In x ys.

Lemma listIncl_refl {A : Type} (xs : list A) : listIncl xs xs.
Proof.
  induction xs; unfold listIncl; eauto.
Qed.

Ltac exploit H :=
  match type of H with
   ?A -> _ => let Y := fresh in assert A as Y; [| specialize (H Y); clear Y] end.

Fixpoint Normal {τ} : interpSortEff τ -> Prop :=
  match τ with
    ι t => fun _ => True
  | 1 => fun _ => True
  | σ × κ => fun t => Normal (fst t) /\
                   Normal (snd t)
  | β σ => fun t => (forall y, In y t -> Normal y) /\
                  Sorted (lexOrderInterpSortEff σ) t /\
                  NoDup t
  end.

(*
If you are feeling extra nice, replicate the bug and ask around
Inductive Normal : forall {τ}, interpSortEff τ -> Prop :=
  normal_ι : forall x : interpSortEff ι, Normal x
| normal_β : forall {τ} {xs : interpSortEff (β τ)},
                            Sorted (lexOrderInterpSortEff τ) xs ->
                            NoDup xs ->
                            (forall y, In y xs -> Normal y) ->
                            Normal xs
| normal_pair : forall {τ σ t}, Normal (fst t) -> Normal (snd t) -> @Normal (τ × σ) t.
*)

Lemma normaliseInterpSortEff_fixed_point {τ} :
  forall t : interpSortEff τ, Normal t -> normaliseInterpSortEff t = t.
Proof.
 induction τ; intros; simpl in *; auto; fold interpSortEff in *.
 + destruct t. reflexivity.
 + unfold normaliseListRepr; destruct H as [? [? ?]].
   rewrite (map_ext_in _ id), map_id; auto.
   rewrite nodup_fixed_point, insertSort_fixed_point; auto.
 + destruct t, H; simpl in *; rewrite IHτ1, IHτ2; auto.
Qed.

Lemma Normal_normaliseInterpSortEff {τ} :
  forall t : interpSortEff τ, Normal (normaliseInterpSortEff t).
Proof.
  induction τ; intros; simpl in *; auto; fold interpSortEff; repeat (repeat split; intros).
  - apply normaliseList_member, in_map_iff in H.
    destruct H as [? [? _]]; subst; auto.
  - unfold normaliseListRepr. 
    apply Sorted_insertSort.
  - apply insertSort_nodup_preserv.
    apply NoDup_nodup.
  - destruct t; simpl; auto.
  - destruct t; simpl; auto.
Qed.

Lemma Normal_interpStxEff {X τ} {Σ : X -> _} (t : nrc__stx Σ τ) ρ :
  Normal (interpStxEff t ρ).
Proof.
  revert ρ; induction t; intros;
  try apply Normal_normaliseInterpSortEff || apply IHt ||
   (unfold normaliseListRepr; repeat split;
     [| apply Sorted_insertSort; auto; fail
      | apply insertSort_nodup_preserv, NoDup_nodup; fail]);
  simpl in *; auto; fold interpSortEff in *.
  + repeat split; constructor || intros ? [].
  + repeat split; repeat constructor; eauto.
    intros ? [|[]]; subst; auto.
  + intros ? H; apply normaliseList_member, in_app_iff in H; destruct H;
    [edestruct IHt1| edestruct IHt2]; eauto.
  + intros ? H; apply normaliseList_member, in_concat in H.
    destruct H as [? [H ?]]; apply in_map_iff in H; destruct H as [z [? ?]]; subst.
    edestruct IHt2 as [H' _]; eapply (H' _ H0).
  + repeat split; edestruct (IHt1 ρ) as [? [? ?]]; intros.
    - apply H; apply listSubtr_in in H2; destruct H2; auto.
    - apply listSubtr_Sorted; auto.
    - apply listSubtr_NoDup; auto.
Qed.

(*
Lemma SortedMin {X} O : forall xs ys : list X, forall x y,
  Sorted O (x :: xs) -> forall z, In z (x :: xs) -> y ⊑ O ? x = true.
  intros ? ? ? ? H H' ?; inversion H; inversion H'; clear H H'; subst.
  apply H_app0; auto.
*)

Lemma NormalList_extEq {X} O :
  forall xs ys : list X,
    NoDup xs -> Sorted O xs
    -> NoDup ys -> Sorted O ys
    -> (forall z, In z xs <-> In z ys) -> xs = ys.
Proof.
  induction xs; intros.
  + symmetry; apply incl_l_nil; intros ? ?; apply H3; auto.
  + inversion H; inversion H0; clear H H0; subst.
    inversion H1; clear H1; subst.
    - exfalso; apply (H3 a); left; reflexivity.
    - inversion H2; subst; clear H2.
      assert (a = x).
      {
        destruct (H3 a) as [H' _]; exploit H'; [left; reflexivity |].
        destruct H'; subst; auto.
        destruct (H3 x) as [_ H']; exploit H'; [left; reflexivity |].
        destruct H'; subst; auto.
        apply (ordAntisymmetry O); auto.
      }
      subst; f_equal.
      apply IHxs; auto.
      intros z; specialize (H3 z); split;
      [destruct H3 as [H3 _]| destruct H3 as [_ H3]]; intros; destruct H3;
      subst; try contradiction; try right; auto.
Qed.      

Lemma eq2eqv : forall P Q, P = Q -> P <-> Q.
Proof.
  intros; subst; tauto.
Qed.

Lemma eff2Prop_Normal_injec {τ} (x y : interpSortEff τ) :
  Normal x -> Normal y ->
  eff2Prop x = eff2Prop y -> x = y.
Proof.
  revert x y; induction τ; simpl in *; intros; eauto; fold interpSortEff interpSortProp in *.
  - destruct x. destruct y. reflexivity.
  - destruct H as [? [? ?]], H0 as [? [? ?]].
    eapply NormalList_extEq; eauto.
    intros z; apply f_equal with (f := fun h => h (eff2Prop z)), eq2eqv in H1.
    destruct H1; split; intros.
    + assert (Normal z) by auto.
      eapply in_map in H7; specialize (H1 H7). apply in_map_iff in H1.
      destruct H1 as [u [H1 H12]].
      assert (u = z) by (apply IHτ; auto); subst; auto.
    + assert (Normal z) by auto.
      eapply in_map in H7; specialize (H6 H7). apply in_map_iff in H6.
      destruct H6 as [u [H6 H62]].
      assert (u = z) by (apply IHτ; auto); subst; auto.
  - destruct x, y, H, H0; subst; simpl in *.
    injection H1; intros; rewrite (IHτ1 i i1), (IHτ2 i0 i2); eauto.
Qed.


Lemma eff2Prop_normalise_compat {τ} :
  forall x : interpSortEff τ, eff2Prop (normaliseInterpSortEff x) = eff2Prop x.
Proof.
  intros x; revert x.
  induction τ; auto.
  + intros. simpl; fold interpSortProp in *. extensionality z; apply propositional_extensionality.
    fold interpSortProp in *; specialize (Normal_normaliseInterpSortEff x); intros.
    revert z; simpl. 
    simpl.
    split; intro.
    - apply in_map_iff in H0; fold @eff2Prop in *; destruct H0 as [? [? ?]]; subst.
      destruct H as [? [? ?]]; fold @interpSortEff in *.
      specialize (H _ H1).
      simpl.
      apply normaliseList_member, in_map_iff in H1; destruct H1 as [? [? ?]]; subst.
      rewrite IHτ; apply in_map; auto.
    - apply in_map_iff in H0; destruct H0 as [? [? ?]]; subst.
      rewrite <-IHτ.
      apply in_map, normaliseList_member, in_map; auto.
  + intros [? ?]; simpl in *; apply f_equal2; auto.
Qed.

(* Then we can show compatibility of the two semantics.
    TODO: refine the code a bit so it doesn't look like spaghetti. *)
Lemma effPropCompat {X} {Σ : X -> _} {τ} (t : nrc__stx Σ τ) ρ :
  eff2Prop (interpStxEff t ρ) = interpStxProp t (eff2Prop ∘ ρ).
Proof.
  (* Trivial cases resolved by reflexivity *)
  induction t; simpl; try reflexivity.
  - apply eff2Prop_normalise_compat.
  (* Pair case *)
  - apply f_equal2; auto.
  (* Projection 1 case *)
  - rewrite <- IHt. simpl. destruct interpStxEff.
    simpl. reflexivity.
  (* Projection 2 case *)
  - rewrite <- IHt. simpl. destruct interpStxEff.
    simpl. reflexivity.
  (* Singleton set case *)
  - fold interpSortProp.
    extensionality z.
    apply propositional_extensionality.
    split; intros H.
    + destruct H as [H | H].
      * rewrite <- IHt. symmetry. apply H.
      * destruct H.
    + left. rewrite IHt. symmetry. apply H.
  (* Small cup case *)
  - extensionality z. apply propositional_extensionality.
    split; intros H.
    + rewrite <- IHt1. rewrite <- IHt2.
      apply in_map_iff in H. destruct H as [x [E_x H]].
      subst. apply normaliseList_member in H. apply in_app_or in H.
      destruct H as [H | H].
      * left. simpl. apply in_map. apply H.
      * right. simpl. apply in_map. apply H.
    + destruct H as [H | H].
      * rewrite <- IHt1 in H. simpl in H.
        apply in_map_iff in H. destruct H as [x [E_x H]].
        subst. apply in_map. apply normaliseList_member.
        apply in_or_app. left. apply H.
      * rewrite <- IHt2 in H. simpl in H.
        apply in_map_iff in H. destruct H as [x [E_x H]].
        subst. apply in_map. apply normaliseList_member.
        apply in_or_app. right. apply H.
  (* Big cup case *)
  - simpl. fold interpSortProp. extensionality z.
    apply propositional_extensionality.
    split; intros H; simpl.
    + apply in_map_iff in H. destruct H as [x [E_x H]]. subst.
      apply normaliseList_member in H. apply in_concat in H.
      destruct H as [xs [H1 H2]]. apply in_map_iff in H1.
      destruct H1 as [y [H11 H12]]. subst. exists (eff2Prop y).
      split.
      * rewrite <- IHt1. simpl. apply in_map. apply H12.
      * simpl in IHt2. specialize (IHt2 (ρ & y)).
        apply (f_equal (fun y => y (eff2Prop x))) in IHt2.
        assert (HInterpFunEq :
                  (fun x : ^ X => eff2Prop (option_rect (interpSortEff ∘ Σ & σ) ρ y x))
                  = (option_rect (interpSortProp ∘ Σ & σ)
                                (fun x0 : X => eff2Prop (ρ x0)) (eff2Prop y))
        ).
        { extensionality z. destruct z; simpl; reflexivity. }
        rewrite HInterpFunEq in IHt2. rewrite <- IHt2. apply in_map.
        apply H2.
    + destruct H as [y [H1 H2]]. apply in_map_iff.
      specialize (IHt1 ρ). rewrite <- IHt1 in H1.
      simpl in H1. apply in_map_iff in H1. destruct H1 as [x [H1 H12]].
      subst. rename H12 into H1. specialize (IHt2 (ρ & x)).
      assert (H_e2P_ordering : 
              (option_rect (interpSortProp ∘ Σ & σ) (fun x : X => eff2Prop (ρ x)) (eff2Prop x))
                = fun y => eff2Prop (option_rect (interpSortEff ∘ Σ & σ) ρ x y)).
      { extensionality p. destruct p as [p | ]; simpl; reflexivity. }
      rewrite <- H_e2P_ordering in IHt2. rewrite <- IHt2 in H2. simpl in H2.
      apply in_map_iff in H2. destruct H2 as [y [H21 H22]]. exists y.
      split.
      * apply H21.
      * apply normaliseList_member. apply in_concat. subst.
        fold interpSortEff in *.
        eexists; split; [|exact H22].
        apply in_map_iff.
        eexists; split; [reflexivity|].
        exact H1.
  - simpl. extensionality q. fold interpSortProp in q.
    rewrite <- IHt1. rewrite <- IHt2.
    apply propositional_extensionality.
    split; simpl; intros H.
    + apply (in_map_iff) in H. destruct H as [q' [H1 H2]]. subst.
      apply listSubtr_in in H2. split.
      * apply in_map. destruct H2 as [H1 H2]. apply H1.
      * intros Hneg. destruct H2 as [H1 H2]. apply in_map_iff in Hneg.
        destruct Hneg as [x [Hneg1 Hneg2]].
        destruct (Normal_interpStxEff t1 ρ) as [? _]; subst.
        destruct (Normal_interpStxEff t2 ρ) as [? _]; subst.
        fold interpSortEff in *.
        apply eff2Prop_Normal_injec in Hneg1; subst;
        (apply H; auto; fail) || (apply H0; auto; fail) || auto.
    + destruct H as [H H']; apply in_map_iff in H; destruct H as [? [? ?]]; subst.
      apply in_map, listSubtr_in; split; auto.
      intro; apply H'; apply in_map; auto.
  Qed.
End Sem.
