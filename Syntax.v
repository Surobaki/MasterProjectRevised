(* Ad-hoc base types for concrete examples *)
Inductive baseTy : Type := ty_nat | ty_str | ty_bool.

Require Import Strings.String.

(* Base type interpretation in Coq *)
Definition interpBase (t : baseTy) : Type :=
match t with
| ty_nat => nat
| ty_str => string
| ty_bool => bool
end.

(* Define in-language typing *)
Inductive sort : Type :=
| sort_atom : baseTy -> sort
| sort_unit : sort
| sort_pow  : sort -> sort
| sort_prod : sort -> sort -> sort.

Definition ctx__empty : False -> sort :=
  fun x => match x with end.

Declare Scope sort_scope.
Bind Scope sort_scope with sort.

Notation "'1'"   := sort_unit : sort_scope.
Notation "'ι'"   := sort_atom : sort_scope.
Notation "'β'"   := sort_pow : sort_scope.
Notation "/O"    := ctx__empty : sort_scope.
Notation "τ × σ" := (sort_prod τ σ) (at level 62) : sort_scope.
Notation "θ & A" := (@option_rect _ (fun _ => _) θ A) (at level 41) : sort_scope.
Notation "^ X"   := (option X) (at level 5) : type_scope.
Notation "⟨π xy" := (fst xy) (at level 74, no associativity) : type_scope.
Notation "⟩π xy" := (snd xy) (at level 74, no associativity) : type_scope.

Open Scope sort_scope.

(* Core syntax *)
Inductive nrc__stx {X : Type} (Σ : X -> sort) : sort -> Type :=
| nrc_var (x : X) : nrc__stx Σ (Σ x)
| nrc_pair (τ σ : sort) (H1 : nrc__stx Σ τ) (H2 : nrc__stx Σ σ) 
  : nrc__stx Σ (τ × σ)
| nrc_proj1 (τ σ : sort) (H : nrc__stx Σ (τ × σ)) 
  : nrc__stx Σ τ
| nrc_proj2 (τ σ : sort) (H : nrc__stx Σ (τ × σ)) 
  : nrc__stx Σ σ
| nrc_unit : nrc__stx Σ 1
| nrc_empty (τ : sort) : nrc__stx Σ (β τ)
| nrc_sing (τ : sort) (H : nrc__stx Σ τ) : nrc__stx Σ (β τ)
| nrc_cup (τ : sort) (H1 : nrc__stx Σ (β τ)) (H2 : nrc__stx Σ (β τ))
  : nrc__stx Σ (β τ)
| nrc_bigcup (τ σ : sort) (H1 : nrc__stx Σ (β σ)) (H2 : @nrc__stx ^X (Σ & σ) (β τ))
  : nrc__stx Σ (β τ)
| nrc_diff (τ : sort) (H1 : nrc__stx Σ (β τ)) (H2 : nrc__stx Σ (β τ))
  : nrc__stx Σ (β τ).
