(** Coq coding by choukh, Oct 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Axiom.Separation.
Require Import BBST.Axiom.Infinity.
Require Import BBST.Definition.Singleton.
Require Import BBST.Definition.Omega.

Module 错误示范.

Axiom ℕ : 集合.

Axiom 零是自然数 : ∅ ∈ ℕ.
Axiom 一是自然数 : ∅⁺ ∈ ℕ.
Axiom 二是自然数 : ∅⁺⁺ ∈ ℕ.
Axiom 三是自然数 : ∅⁺⁺⁺ ∈ ℕ.

Axiom 以此类推 : ∀n ∈ ℕ, n⁺ ∈ ℕ.

Axiom 这不是自然数 : {{∅,},} ∉ ℕ.
Axiom 这也不是自然数 : {{{∅,},},} ∉ ℕ.
(* ヽ(`Д´)ﾉ *)

End 错误示范.

Theorem 非零自然数的前驱存在 : ∀n ∈ ω, n ≠ ∅ → ∃k ∈ ω, n = k⁺.
Proof.
  intros n Hn.
  set {n ∊ ω | n ≠ ∅ → ∃k ∈ ω, n = k⁺} as N.
  assert (相等: N = ω). {
    apply 归纳原理.
    - intros x Hx. now apply 分离之父集 in Hx.
    - split.
      + (* n = ∅ *)
        apply 分离介入. auto. intros 矛盾. easy.
      + (* n = m⁺ *)
        intros m Hm.
        apply 分离除去 in Hm as [Hm 归纳条件].
        apply 分离介入. apply ω归纳. apply Hm.
        intros _. exists m. split; easy.
  }
  rewrite <- 相等 in Hn. now apply 分离之条件 in Hn.
Qed.

(* 练习5-1 *)
Fact 零小于后继数 : ∀n ∈ ω, ∅ ∈ n⁺.
Proof.
  (* 不使用auto *)
Admitted.
