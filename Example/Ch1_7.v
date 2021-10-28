(** Coq coding by choukh, Oct 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Axiom.Separation.
Require Import BBST.Definition.Omega.
Require Import BBST.Definition.EpsilonOrdering.
Require Import BBST.Theory.OrderingOnOmega.

(* ω的任意非空子集有最小数 *)
Theorem ω是ϵ良基 : ϵ良基 ω.
Proof with auto.
  intros N 非空 子集. 反证.
  rewrite ϵ全序则无ϵ最小元即总有ϵ更小 in 反设...
  cut (∀n ∈ ω, n ∉ N). firstorder using 非空介入.
  归纳; intros HnN.
  - apply 反设 in HnN as [m [_ 矛盾]]. 空集归谬.
  - (* 需要把“比m小的数都不属于N”纳入归纳假设 *)
Abort.

(* 练习7-1 *)
Theorem ω是ϵ良基_不使用firstorder : ϵ良基 ω.
Proof with auto.
  intros N 非空 子集. 反证.
  rewrite ϵ全序则无ϵ最小元即总有ϵ更小 in 反设...
  (* 不使用firstorder *)
Admitted.

Fact 零小于后继数_强归纳 : ∀n ∈ ω, ∅ ∈ n⁺.
Proof.
  强归纳. apply 包含即小于后继. apply 零是自然数. apply Hn.
  apply 空集是任意集合的子集.
Qed.

(* 练习7-2 *)
Theorem ω为传递集_强归纳 : 为传递集 ω.
Proof.
  apply 传递集即其元素都为其子集. 强归纳.
  (* 要求：使用强归纳策略，但不使用auto *)
Admitted.

Fact 零小于后继数_强归纳_反证 : ∀n ∈ ω, ∅ ∈ n⁺.
Proof.
  强归纳_反证.
  - apply 右后继介入.
  - intros H0. apply 归纳假设. apply 左后继介入. apply H0.
Qed.

(* 练习7-3 *)
Fact ω为传递集_强归纳_反证 : 为传递集 ω.
Proof.
  apply 传递集即其元素都为其子集. 强归纳_反证.
  (* 要求：使用强归纳_反证策略，但不使用auto *)
Admitted.
