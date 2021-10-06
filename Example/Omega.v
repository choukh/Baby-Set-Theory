(** Coq coding by choukh, Oct 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Axiom.Separation.
Require Import BBST.Axiom.Infinity.
Require Import BBST.Definition.Emptyset.
Require Import BBST.Definition.Successor.
Require Import BBST.Definition.Omega.

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
