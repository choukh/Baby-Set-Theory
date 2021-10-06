(** Coq coding by choukh, Oct 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Axiom.Extensionality.
Require Import BBST.Definition.Include.
Require Import BBST.Definition.Emptyset.
Require Import BBST.Definition.Singleton.
Require Import BBST.Definition.BinaryUnion.
Require Import BBST.Definition.OneTwo.

Definition 后继 := λ a, a ∪ {a,}.
Notation "a ⁺" := (后继 a) (at level 6, format "a ⁺") : 集合域.

Lemma 后继介入 : ∀ a, a ∈ a⁺.
Proof. intros. apply 右并介入. auto. Qed.

Lemma 后继除去 : ∀ a, ∀x ∈ a⁺, x ∈ a ∨ x = a.
Proof.
  intros a x Hx. apply 二元并除去 in Hx as []. auto.
  apply 单集除去 in H. auto.
Qed.

Lemma 含于后继 : ∀ a, a ⊆ a⁺.
Proof. intros. now apply 左并介入. Qed.

Lemma 后继非空 : ∀ a, a⁺ ≠ ∅.
Proof.
  intros a H. eapply 空集除去 in H. apply H.
  apply 后继介入.
Qed.

Global Hint Immediate 后继介入 含于后继 后继非空 : core.

Fact 零的后继为壹 : ∅⁺ = 壹.
Proof.
  外延.
  - apply 后继除去 in H as []. 空集归谬.
    subst. apply 壹介入.
  - apply 壹除去 in H. subst. auto.
Qed.

Fact 壹的后继为贰 : 壹⁺ = 贰.
Proof.
  外延.
  - apply 后继除去 in H as [].
    + apply 壹除去 in H. subst. apply 贰介入0.
    + subst. apply 贰介入1.
  - apply 贰除去 in H as []; subst.
    + apply 含于后继. apply 壹介入.
    + auto.
Qed.
