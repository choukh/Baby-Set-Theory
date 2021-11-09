(** Coq coding by choukh, Oct 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Definition.Omega.
Require Import BBST.Definition.NatEmbedding.
Require Import BBST.Arith.Nat.

Local Coercion 自动嵌入 := λ n, 嵌入 n.

Example 九小于十 : 9 ∈ 10.
Proof. simpl. auto. Qed.

(* 练习15-1 *)
Example 二加三等于五 : 2 + 3 = 5. Admitted.

(* 练习15-2 *)
Example 二乘三等于六 : 2 * 3 = 6. Admitted.

(* 练习15-3 *)
Example 二的三次方等于八 : 2 ^ 3 = 8. Admitted.
