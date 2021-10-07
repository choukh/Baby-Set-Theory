(** Coq coding by choukh, Oct 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Axiom.Extensionality.
Require Import BBST.Axiom.Union.
Require Import BBST.Definition.Include.
Require Import BBST.Definition.Singleton.
Require Import BBST.Definition.BinaryUnion.
Require Import BBST.Definition.Successor.

Definition 为传递集 := λ c, ∀ a b, a ∈ b → b ∈ c → a ∈ c.

(* 集合A是传递集当且仅当A的任意元素都是A的子集 *)
Theorem 传递集即其元素都为其子集 : ∀ A, 为传递集 A ↔ ∀a ∈ A, a ⊆ A.
Proof.
  split.
  - intros 传递 a Ha x Hx. eapply 传递; eauto.
  - intros 子集 x y Hx Hy. eapply 子集; eauto.
Qed.

(* 集合A是传递集当且仅当A的并是A的子集 *)
Theorem 传递集即其并为其子集 : ∀ A, 为传递集 A ↔ ⋃ A ⊆ A.
Proof.
  split.
  - intros 传递 x Hx.
    apply 并集除去 in Hx as [y [Hy Hx]]. eapply 传递; eauto.
  - intros 子集 x y Hx Hy. apply 子集.
    eapply 并集介入; eauto.
Qed.

(* 集合A是传递集当且仅当A的后继的并等于A *)
Theorem 传递集即其后继的并等于自身 : ∀ A, 为传递集 A ↔ ⋃ A⁺ = A.
Proof.
  intros. unfold 后继.
  rewrite 二元并的并等于并的二元并, 单集之并.
  split; intros.
  - 外延 Hx.
    + rewrite 传递集即其并为其子集 in H.
      apply 二元并除去 in Hx as []; auto.
    + apply 右并介入; auto.
  - rewrite 传递集即其并为其子集.
    intros x Hx. rewrite <- H. apply 左并介入; auto.
Qed.
