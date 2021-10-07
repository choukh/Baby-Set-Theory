(** Coq coding by choukh, Oct 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Definition.Include.
Require Import BBST.Definition.Emptyset.
Require Import BBST.Definition.TransitiveSet.
Require Import BBST.Definition.Successor.
Require Import BBST.Definition.Omega.
Require Import BBST.Definition.EpsilonOrdering.

Lemma 小于等于即小于后继 : ∀ n m ∈ ω, n ⋸ m ↔ n ∈ m⁺.
Proof.
  intros n Hn m Hm. split.
  - intros []. auto. subst. auto.
  - intros H. apply 后继除去 in H as [].
    now left. now right.
Qed.

Theorem 后继保序 : ∀ n m ∈ ω, n ∈ m ↔ n⁺ ∈ m⁺.
Proof with auto.
  intros n Hn m Hm. split; intros 小于.
  - generalize dependent n.
    归纳 m; intros n Hn 小于.
    + 空集归谬.
    + apply 小于等于即小于后继...
      apply 后继除去 in 小于 as [].
      * left. apply 归纳假设...
      * subst...
  - apply 小于等于即小于后继 in 小于 as []...
    + apply 自然数传递 with n⁺...
    + subst...
Qed.

(* 自然数的后继是大于该数的最小数 *)
Corollary 小于即后继小于等于 : ∀ n m ∈ ω, n ∈ m ↔ n⁺ ⋸ m.
Proof with auto.
  intros n Hn m Hm. split; intros 小于.
  - apply 后继保序 in 小于...
    apply 小于等于即小于后继 in 小于...
  - apply 小于等于即小于后继 in 小于...
    apply 后继保序...
Qed.

Theorem 自然数反自反 : ∀n ∈ ω, n ∉ n.
Proof.
  intros n Hn. 归纳 n; intros 反设.
  空集归谬. apply 归纳假设. apply 后继保序; auto.
Qed.
