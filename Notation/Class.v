(** Coq coding by choukh, Oct 2021 **)

Require Import BBST.Axiom.Meta.

Notation 类 := 性质.

Definition 类属于 := λ x (C : 类), C x.
Notation "x ⋵ C" := (类属于 x C) (at level 70) : 集合域.

Notation "∀ x .. y ⋵ C , P" :=
  (∀ x, x ⋵ C → (.. (∀ y, y ⋵ C → P) ..))
  (at level 200, x binder, right associativity) : 集合域.

Notation "∃ x .. y ⋵ C , P" :=
  (∃ x, x ⋵ C ∧ (.. (∃ y, y ⋵ C ∧ P) ..))
  (at level 200, x binder, right associativity) : 集合域.

Notation "'∃' ! x .. y ⋵ C , P" :=
  (∃! x, x ⋵ C ∧ (.. (∃! y, y ⋵ C ∧ P) ..))
  (at level 200, x binder, right associativity,
   format "'[' '∃' ! '/ '  x .. y  ⋵  C ,  '/ ' P ']'") : 集合域.


Definition 为真类 := λ C, ¬ ∃ A, ∀x ⋵ C, x ∈ A.
Definition 为传递类 := λ C, ∀ A B, A ∈ B → B ⋵ C → A ⋵ C.

(* 子类 *)
Notation "C ⫃ D" := (∀ x, x ⋵ C → x ⋵ D) (at level 70) : 集合域.

(* 类的子集 *)
Notation "A ⪽ C" := (∀ x, x ∈ A → x ⋵ C) (at level 70) : 集合域.
