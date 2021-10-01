(** Coq coding by choukh, Sep 2021 **)

Require Import BBST.Axiom.Meta.

Axiom 外延公理 : ∀ A B, (∀ x, x ∈ A ↔ x ∈ B) → A = B.

Tactic Notation "外延" :=
  apply 外延公理; split; intros.
Tactic Notation "外延" ident(H) :=
  apply 外延公理; split; intros H.
Tactic Notation "外延" ident(x) ident(H) :=
  apply 外延公理; intros x; split; intros H.
