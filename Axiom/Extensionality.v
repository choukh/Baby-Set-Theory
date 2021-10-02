(** Coq coding by choukh, Sep 2021 **)

Require Import BBST.Axiom.Meta.

(* 如果两个集合有相等的元素，那么这两个集合相等 *)
Axiom 外延公理 : ∀ A B, (∀ x, x ∈ A ↔ x ∈ B) → A = B.

Tactic Notation "外延" :=
  apply 外延公理; split; intros.
Tactic Notation "外延" ident(H) :=
  apply 外延公理; split; intros H.
Tactic Notation "外延" ident(x) ident(H) :=
  apply 外延公理; intros x; split; intros H.

Fact 相等的集合有相同的元素 :
  ∀ A B, A = B → (∀ x, x ∈ A ↔ x ∈ B).
Proof.
  intros A B Heq x. split; intros Hx.
  - rewrite <- Heq. apply Hx.
  - rewrite Heq. apply Hx.
Qed.
