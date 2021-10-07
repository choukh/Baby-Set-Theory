(** Coq coding by choukh, Oct 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Axiom.Extensionality.
Require Import BBST.Axiom.Union.
Require Import BBST.Axiom.Power.
Require Import BBST.Definition.Include.
Require Import BBST.Definition.TransitiveSet.

(* 练习6-1 *)
Theorem 传递集即其幂是传递集: ∀ A, 为传递集 A ↔ 为传递集 𝒫 A.
Proof.
  (* 不使用firstorder证明 *)
Admitted.

(* 练习6-2 *)
Fact 传递集的并是传递集 : ∀ A, 为传递集 A → 为传递集 ⋃ A.
Proof.
  (* 使用引理"传递集即其并为其子集"证明 *)
Admitted.
