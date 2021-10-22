(** Coq coding by choukh, Oct 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Axiom.Extensionality.
Require Import BBST.Axiom.Separation.
Require Import BBST.Definition.Include.
Require Import BBST.Definition.BinaryUnion.
Require Import BBST.Definition.BinaryIntersect.
Require Import BBST.Definition.Complement.
Require Import BBST.Theory.BasicAlgebraOfSet.

(* 我们可以加入一些只在当前文件起作用的Hint *)
Local Hint Resolve 二元并外介入 : core.
Local Hint Resolve 二元交外介入 : core.
Local Hint Resolve 补集外介入 : core.

Example 练习8_1: ∀ A B, (A ∩ B) ∪ (A - B) = A. Admitted.

Example 练习8_2: ∀ A B, (A ∩ B) ∪ (B - A) = B. Admitted.

Example 练习8_3: ∀ A B, A - (A ∩ B) = A - B. Admitted.

Example 练习8_4: ∀ A B, A - (A - B) = A ∩ B. Admitted.

Example 练习8_5: ∀ A B C, (A ∪ B) - C = (A - C) ∪ (B - C). Admitted.

Example 练习8_6: ∀ A B C, A - (B - C) = (A - B) ∪ (A ∩ C). Admitted.

Example 练习8_7: ∀ A B C, (A - B) - C = A - (B ∪ C). Admitted.

Example 练习8_8: ∀ A B C, A ⊆ C ∧ B ⊆ C ↔ A ∪ B ⊆ C. Admitted.

Example 练习8_9: ∀ A B C, C ⊆ A ∧ C ⊆ B ↔ C ⊆ A ∩ B. Admitted.

Example 练习8_10 : ∀ A B C, (A ∩ B) - (A ∩ C) = (A ∩ B) - C. Admitted.

Example 练习8_11: ∀ A B C,
  ((A ∪ B ∪ C) ∩ (A ∪ B)) - ((A ∪ (B - C)) ∩ A) = B - A.
Proof.
  (* 提示：可以用“二元交交换律”，“交并吸收律”等rewrite，而不需要外延 *)
Admitted.
