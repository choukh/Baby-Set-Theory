(** Coq coding by choukh, Oct 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Axiom.Separation.

(* 由A中那些自己不属于自己的元素组成的集合 *)
Definition 罗素集 := λ A, {x ∊ A | x ∉ x}.

Theorem 罗素集性质 : ∀ A, 罗素集 A ∉ A.
Proof.
  intros.
  排中 (罗素集 A ∈ 罗素集 A) as [正|反].
  - apply 分离除去 in 正 as [属父 条件].
    exfalso. apply 条件. now apply 分离介入.
  - intros 属父. apply 反. now apply 分离介入.
Qed.

Theorem 无大全集 : ¬ ∃ A, ∀ x, x ∈ A.
Proof.
  intros [A H]. eapply 罗素集性质. apply H.
Qed.
