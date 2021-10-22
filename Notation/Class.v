(** Coq coding by choukh, Oct 2021 **)

Require Import BBST.Axiom.Meta.

Notation 类 := 性质.

Definition 类属于 := λ x (C : 类), C x.
Notation "x ⋵ C" := (类属于 x C) (at level 70) : 集合域.
Global Hint Unfold 类属于 : core.

Definition 为集合 := λ C, ∃ A, ∀ x, x ∈ A ↔ x ⋵ C.

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

(* 子类 *)
Notation "C ⫃ D" := (∀ x, x ⋵ C → x ⋵ D) (at level 70) : 集合域.

(* 类的子集 *)
Notation "A ⪽ C" := (∀ x, x ∈ A → x ⋵ C) (at level 70) : 集合域.
