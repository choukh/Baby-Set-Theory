(** Coq coding by choukh, Sep 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Axiom.Extensionality.
Require Import BBST.Axiom.Separation.

Axiom 至少有 : 集合 → 集合 → 集合.
Axiom 配对公理 : ∀ a b, a ∈ 至少有 a b ∧ b ∈ 至少有 a b.

Definition 配对 := λ a b, {x ∊ 至少有 a b | x = a ∨ x = b}.
Notation "{ a , b }" := (配对 a b) : 集合域.

Lemma 左配对介入 : ∀ a b, a ∈ {a, b}.
Proof. intros. apply 分离介入. apply 配对公理. now left. Qed.

Lemma 右配对介入 : ∀ a b, b ∈ {a, b}.
Proof. intros. apply 分离介入. apply 配对公理. now right. Qed.

Lemma 配对除去 : ∀ a b, ∀x ∈ {a, b}, x = a ∨ x = b.
Proof. intros. now apply 分离之条件 in H. Qed.

Global Opaque 配对.

Global Hint Immediate 左配对介入 右配对介入 : core.

Lemma 配对与顺序无关 : ∀ a b, {a, b} = {b, a}.
Proof.
  intros. 外延;
  apply 配对除去 in H as []; rewrite H; auto.
Qed.
