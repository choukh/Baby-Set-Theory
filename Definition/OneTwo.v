(** Coq coding by choukh, Oct 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Axiom.Extensionality.
Require Import BBST.Axiom.Separation.
Require Import BBST.Axiom.Pairing.
Require Import BBST.Axiom.Union.
Require Import BBST.Axiom.Power.
Require Import BBST.Definition.Include.
Require Import BBST.Definition.Emptyset.
Require Import BBST.Definition.Singleton.

Definition 壹 := {∅,}.

Lemma 壹介入 : ∅ ∈ 壹.
Proof. apply 单集介入. Qed.

Lemma 壹除去 : ∀ x, x ∈ 壹 → x = ∅.
Proof. intros. now apply 单集除去. Qed.

Lemma 壹的子集为零或壹 : ∀ x, x ⊆ 壹 → x = ∅ ∨ x = 壹.
Proof. apply 单集的子集是空集或该单集. Qed.

Lemma 壹之并为零 : ⋃ 壹 = ∅.
Proof. apply 单集之并. Qed.

Lemma 零之幂为壹 : 𝒫 ∅ = 壹.
Proof. exact 空集之幂. Qed.

Lemma 只有零或壹之并为零 : ∀ x, ⋃ x = ∅ ↔ x = ∅ ∨ x = 壹.
Proof with eauto.
  split; intros.
  - destruct (空集排中 x) as [Hx0|[a Ha]]. left...
    destruct (空集排中 a) as [Ha0|[b Hb]].
    + right. 外延 y Hy.
      * destruct (空集排中 y) as [Hy0|[c Hc]].
        -- subst. apply 壹介入.
        -- exfalso. eapply 空集除去 in H. apply H. eapply 并集介入...
      * apply 单集除去 in Hy. subst...
    + exfalso. eapply 空集除去 in H. apply H. eapply 并集介入...
  - destruct H; subst.
    + apply 空集之并.
    + apply 壹之并为零.
Qed.

Definition 贰 := {∅, 壹}.

Lemma 贰介入0 : ∅ ∈ 贰.
Proof. apply 左配对介入. Qed.

Lemma 贰介入1 : 壹 ∈ 贰.
Proof. apply 右配对介入. Qed.

Lemma 贰除去 : ∀ x, x ∈ 贰 → x = ∅ ∨ x = 壹.
Proof. intros. now apply 配对除去. Qed.

Lemma 贰之并为壹 : ⋃ 贰 = 壹.
Proof.
  外延.
  - apply 并集除去 in H as [a [Ha Hx]].
    apply 贰除去 in Ha as []; subst. 空集归谬. auto.
  - eapply 并集介入; eauto. apply 贰介入1.
Qed.

Lemma 壹之幂为贰 : 𝒫 壹 = 贰.
Proof. apply 单集之幂. Qed.
