(** Coq coding by choukh, Oct 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Axiom.Separation.

Definition 罗素集 := λ A, {x ∊ A | x ∉ x}.

Theorem 罗素集规范 : ∀ A, 罗素集 A ∉ A.
Proof.
  intros.
  排中 (罗素集 A ∈ 罗素集 A).
  - apply 分离除去 in H as [Hin Hout]. exfalso.
    apply Hout. now apply 分离介入.
  - intros Hin. apply H. now apply 分离介入.
Qed.

Theorem 无大全集 : ¬ ∃ A, ∀ x, x ∈ A.
Proof.
  intros [A H].
  specialize H with (罗素集 A).
  now apply 罗素集规范 with A.
Qed.
