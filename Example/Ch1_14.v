(** Coq coding by choukh, Oct 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Definition.Omega.
Require Import BBST.Definition.NatEmbedding.

Fact 零不是后继 : ∀ n : nat, O ≠ S n.
Proof. discriminate. Qed.

Fact 一不等于二 : 1 ≠ 2.
Proof. discriminate. Qed.

Fact 后继是单射 : ∀ n m : nat, S n = S m → n = m.
Proof. intros. inversion H. reflexivity. Qed.

(* 归纳原理 *)
Print nat_ind.

Fact 嵌入0 : 嵌入 0 = ∅.
Proof. simpl. reflexivity. Qed.

Fact 嵌入1 : 嵌入 1 = ∅⁺.
Proof. simpl. reflexivity. Qed.

Fact 嵌入2 : 嵌入 2 = ∅⁺⁺.
Proof. reflexivity. Qed.
