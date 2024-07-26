From NRCFormalisation Require Import Syntax.
From NRCFormalisation Require Import DecidableEquality.
From NRCFormalisation Require Import OrderedTypes.
From NRCFormalisation Require Import Semantics.

Require Ascii.
Require Import String.
Require Import Lists.List.

Open Scope sort_scope.
Open Scope string_scope.
Open Scope list_scope.

(* Notation useful later for nrc__pred predicates *)
Notation "'Bδ'" := (β 1) (at level 70).

Arguments nrc_var {X} {Σ}.
Arguments nrc_pair {X} {Σ} {τ} {σ}.
Arguments nrc_proj1 {X} {Σ} {τ} {σ}.
Arguments nrc_proj2 {X} {Σ} {τ} {σ}.
Arguments nrc_unit {X} {Σ}.
Arguments nrc_empty {X} {Σ} {τ}.
Arguments nrc_sing {X} {Σ} {τ}.
Arguments nrc_cup {X} {Σ} {τ}.
Arguments nrc_bigcup {X} {Σ} {τ}.
Arguments nrc_diff {X} {Σ} {τ}.

Open Scope sort_scope.

(* Term substitution in NRC *)

Definition mapTy {X Y} (Σ : X -> sort) (Γ : Y -> sort) :=
  sigT (fun f => forall x, Γ (f x) = Σ x).

Definition map_add_binder {X Y : Type} (Σ : X -> sort) (Γ : Y -> sort) :
     mapTy Σ Γ -> forall σ, mapTy (Σ & σ) (Γ & σ).
Proof.
  intros f σ. unfold mapTy in *.
  destruct f as [f H].
  exists (option_map f).
  intros. unfold option_map. destruct x; simpl; auto.
Defined.

(* Shorthand *)
Notation mapAB := map_add_binder.

Fixpoint map {X Y} {Σ : X -> sort} {Γ : Y -> sort} {τ : sort}
  (f : mapTy Σ Γ) (t : nrc__stx Σ τ) {struct t} : nrc__stx Γ τ :=
  match t with
  | nrc_var x => match (projT2 f x) in (_ = varSort)
                  return nrc__stx Γ varSort with
                    eq_refl => nrc_var ((projT1 f) x) end
  | nrc_pair π1 π2     => nrc_pair (map f π1) (map f π2)
  | nrc_proj1 x        => nrc_proj1 (map f x)
  | nrc_proj2 x        => nrc_proj2 (map f x)
  | nrc_unit           => nrc_unit
  | nrc_empty          => nrc_empty
  | nrc_sing x         => nrc_sing (map f x)
  | nrc_cup x y        => nrc_cup (map f x) (map f y)
  | nrc_bigcup σ x y   => nrc_bigcup σ (map f x)
                           (map (mapAB Σ Γ f σ) y)
  | nrc_diff x y       => nrc_diff (map f x) (map f y)
  end.

Definition bindTy {X Y : Type} (Σ : X -> sort) (Γ : Y -> sort) :=
  forall (x : X), nrc__stx Γ (Σ x).

Definition bind_add_binder {X Y : Type} (Σ : X -> sort) (Γ : Y -> sort) :
  bindTy Σ Γ -> forall σ, bindTy (Σ & σ) (Γ & σ).
Proof.
  unfold bindTy. intros f σ.
  assert (H : mapTy Γ (Γ & σ)). {
    unfold mapTy. exists Some. simpl. reflexivity. }
  intros [x |].
  - specialize (f x). simpl. apply (map H f).
  - simpl. apply (@nrc_var _ (Γ & σ) None).
Defined.

Notation bindAB := bind_add_binder.

Fixpoint bind {X Y : Type} {Σ : X -> sort} {Γ : Y -> sort} {τ : sort}
  (f : bindTy Σ Γ) (t : nrc__stx Σ τ) {struct t} : nrc__stx Γ τ :=
  match t with
  | nrc_var x => f x
  | nrc_pair π1 π2 => nrc_pair (bind f π1) (bind f π2)
  | nrc_proj1 x => nrc_proj1 (bind f x)
  | nrc_proj2 x => nrc_proj2 (bind f x)
  | nrc_unit => nrc_unit
  | nrc_empty => nrc_empty
  | nrc_sing x => nrc_sing (bind f x)
  | nrc_cup x y => nrc_cup (bind f x) (bind f y)
  | nrc_bigcup σ x y => nrc_bigcup σ (bind f x)
                                  (bind (bindAB Σ Γ f σ) y)
  | nrc_diff x y => nrc_cup (bind f x) (bind f y)
  end.

Definition nrc__pred {X : Type} (Σ : X -> sort) (τ : sort) := nrc__stx (Σ & τ) (Bδ).
Definition nrc_select {X : Type} {Σ : X -> sort} {τ : sort}
  (t : nrc__stx Σ (β τ)) (p : nrc__pred Σ τ) : nrc__stx Σ (β τ).
unfold nrc__pred in p. 
refine (nrc_bigcup _ t _). refine (nrc_bigcup _ p _).
assert (H_map : mapTy Σ ((Σ & τ) & 1)). {
  unfold mapTy. exists (fun x => Some (Some x)). intros.
  reflexivity. }
refine (map H_map _). apply t.
Defined.

Definition nrc_intersect__Bool (τ : sort) :
  @nrc__stx bool (fun _ => β τ) (β τ) :=
    let a := nrc_var true in
    let b := nrc_var false in 
      nrc_diff (nrc_cup a b)
               (nrc_cup (nrc_diff a b)
                        (nrc_diff b a)).

Definition nrc_intersect {X : Type} {τ : sort} {Σ : X -> sort}
  (t1 : nrc__stx Σ (β τ)) (t2 : nrc__stx Σ (β τ)) : nrc__stx Σ (β τ) :=
    nrc_diff (nrc_cup t1 t2)
             (nrc_cup (nrc_diff t1 t2)
                      (nrc_diff t2 t1)).

Definition nrc_equal {X : Type} {Σ : X -> sort} {τ}
  (t1 : nrc__stx Σ τ) (t2 : nrc__stx Σ τ) : nrc__stx Σ (Bδ) :=
  nrc_bigcup τ (nrc_intersect (nrc_sing t1) (nrc_sing t2))
               (nrc_sing nrc_unit).

(* TODO: Write an SQL query that you then show a (working) NRC counterpart *)
Definition nrc_example_1 :
  interpSortEff (β (ι ty_str × ι ty_str × ι ty_nat)) := 
    ("EMP1", "Santana", 100000) :: ("EMP2", "Martyn", 150000) :: 
    ("CTR1", "Chiharu", 500000) :: ("CTR2", "Parveen", 200000) :: nil.
Definition nrc_example_2 :
  interpSortEff (β (β (ι ty_nat) × ι ty_str × ι ty_bool)) :=
  ((10 :: 29 :: 54 :: nil), "Project Iris", true) ::
  ((10 :: 94 :: 95 :: 96 :: nil), "Project Cornea", false) ::
  ((nil), "Project Sclera", true) :: nil.
Definition nrc_example_3 :
  interpSortEff (β (ι ty_str × ι ty_nat × ι ty_nat)) :=
  ("CTR1", 10, 5000) :: ("CTR1", 29, 1000) :: ("EMP2", 94, 500) ::
  ("EMP2", 95, 500) :: ("EMP2", 96, 500) :: nil.

Definition nat_ctxt (n : nat) : sort := 
  match n with
  | 0 => ι ty_nat
  | S O => ι ty_nat
  | 2 => ι ty_nat
  | 3 => ι ty_nat
  | 4 => ι ty_bool
  | 5 => ι ty_bool
  | _ => ι ty_str
  end.

(* Coq bug. Does not infer Σ appropriately, leading to a failure at reasoning 
   with output of (Σ x). *)
Fail Definition nrc_stx1 : 
  nrc__stx nat_ctxt (β (ι ty_str × ι ty_str × ι ty_nat)) :=
  (nrc_cup _
    (nrc_sing (nrc_pair (nrc_pair (nrc_var 8) (nrc_var 6)) (nrc_var 0)))
    (nrc_sing (nrc_pair (nrc_pair (nrc_var 9) (nrc_var 7)) (nrc_var (S O))))).

Definition nrc_stx1 : nrc__stx nat_ctxt (β (ι ty_str × ι ty_str × ι ty_nat)) :=
  (@nrc_cup _ nat_ctxt _
    (@nrc_cup _ nat_ctxt _
      (nrc_sing (nrc_pair (nrc_pair (nrc_var 8) (nrc_var 6)) (nrc_var 0)))
      (nrc_sing (nrc_pair (nrc_pair (nrc_var 9) (nrc_var 7)) (nrc_var (S O)))))
    (nrc_sing (nrc_pair (nrc_pair (nrc_var 8) (nrc_var 6)) (nrc_var 0)))).

(*Definition nrc_stx1_interp : forall (x : string), interpSortEff (str_ctxt x).
intros.*)

Definition interpFun : forall x : nat, interpSortEff (nat_ctxt x) :=
  fun s => match s with
        | 0 => 100000
        | S O => 150000
        | 2 => 500000
        | 3 => 200000
        | 4 => true
        | 5 => false
        | 6 => "Santana"
        | 7 => "Martyn"
        | 8 => "EMP1"
        | 9 => "EMP2"
        | _ => "Whoopsie!"
        end.
  

Definition nrc_example__stx1 :=
  interpStxEff nrc_stx1 interpFun.

Compute (nrc_example__stx1).

Definition nrc_select_atom__stx :
  nrc__stx (/O & β (ι ty_str × ι ty_str) & ι ty_str) (β (ι ty_str × ι ty_str)) :=
  nrc_select (@nrc_var _ ((/O & β (ι ty_str × ι ty_str)) & ι ty_str) (Some None))
             (@nrc_equal _ (((/O & β (ι ty_str × ι ty_str)) & ι ty_str) & (ι ty_str × ι ty_str)) _
                  (nrc_var (Some None))
                  (nrc_proj1 (nrc_var (None)))).


(*Definition nrc_select_atom__sem (input_data : list (string * string))
  (searched_term : string) : list (string * string) :=
    interpStxEff string string_dec lexOrderString nrc_select_atom__stx input_data.
*)

(*
 Dependent function form option option Empty
 The first nothing gets mapped to string
 The some none maps to list of string * string
 Use compute to understand what it wants
 *)

(* TODO: Prove that select works with prop and list semantics as it should. *)

(* TODO: Write a query that is more helpful when written in NRC *)
(* Idea: R ↦ {(x, R^-1(x)) | x ∈ cod(R)} *)

(*
Require Import Classical.

Lemma interTmSpec : forall τ ρ,
  forall x, interpStxProp bool (interTm τ) ρ x <-> ρ true x /\ ρ false x.
  intros.
  fold (interpSortProp bool τ) in *.
  split; intros; simpl in *.
  + destruct H as [[|] ?]; split; auto.
    - apply NNPP; intros ?.
      apply H0; left; split; assumption.
    - apply NNPP; auto. 
  + 
Admitted. 
*)

(*  *)
