(** Coq coding by choukh, Sep 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Axiom.Extensionality.
Require Import BBST.Axiom.Pairing.
Require Import BBST.Axiom.Power.
Require Import BBST.Definition.Emptyset.
Require Import BBST.Definition.Singleton.
Require Import BBST.Definition.BinaryUnion.
Require Import BBST.Definition.OrderedPair.
Require Import BBST.Definition.Product.

Module 错误的有序对.

Definition 有序对 := λ a b, {a, {b,}}.

Fact 有歧义 : 有序对 {∅,} {∅,} = 有序对 {{∅,},} ∅.
Proof. unfold 有序对. apply 配对与顺序无关. Qed.

End 错误的有序对.

Fact 有序对的递归定义 : ∀ a b c, <a, b, c> = <<a, b>, c>.
Proof. reflexivity. Qed.

Example 有序对化简 : ∀ a b, 右 <a, 左 <a, b>> = a.
Proof. intros a b. 化简. Qed.

Example 测试_有序对分离介入1 : {'<x, y> ∊ {<∅, ∅>, <∅, {∅,}>} | x = y} = {<∅, ∅>,}.
Proof with auto.
  intros. 外延.
  - 有序对分离|-H. apply 配对除去 in Hp as [].
    + apply 有序对相等 in H0 as []; subst...
    + apply 有序对相等 in H0 as []; subst.
      exfalso. apply 非空除去 with ∅... exists ∅. rewrite H at 2...
  - 有序对分离-|with ∅ ∅. now apply 单集除去 in H.
Qed.

Example 测试_有序对分离介入2 : <∅, ∅> ∈ {'<x, y> ∊ {<∅, ∅>, <∅, {∅,}>} | x = y}.
Proof. 有序对分离-|. Qed.

(* 练习9-1 *)
Fact 直积是单射: ∀ A B C, 非空 A → A × B = A × C → B = C.
Proof with auto.
Admitted.
