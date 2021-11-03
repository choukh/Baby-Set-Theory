(** Coq coding by choukh, Oct 2021 **)

Require Import BBST.Theory.Ordinal.
Require Import BBST.Theory.OrdinalOperation.

Section 序数递归.
Variable y₀ : 集合.
Variable F : 函数类型.

Definition 序数递归 := 序数递归 y₀ F.

Fact 序数递归的前段性质 : ∀α ⋵ 𝐎𝐍, ∀β ∈ α, (序数递归 ↑ β⁺)[β] = (序数递归 ↑ α)[β].
Proof. intros. rewrite <- 类函数限制之应用, <- 类函数限制之应用; auto. Qed.

End 序数递归.
