(** Coq coding by choukh, Oct 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Definition.Include.
Require Import BBST.Definition.Emptyset.
Require Import BBST.Definition.TransitiveSet.
Require Import BBST.Definition.Successor.
Require Import BBST.Definition.Omega.
Require Import BBST.Definition.EpsilonOrdering.

Lemma 小于等于即小于后继 : ∀ n m ∈ ω, n ⋸ m ↔ n ∈ m⁺.
Proof.
  intros n Hn m Hm. split.
  - intros []. auto. subst. auto.
  - intros H. apply 后继除去 in H as [].
    now left. now right.
Qed.

Theorem 后继保序 : ∀ n m ∈ ω, n ∈ m ↔ n⁺ ∈ m⁺.
Proof with auto.
  intros n Hn m Hm. split; intros 小于.
  - generalize dependent n.
    归纳 m; intros n Hn 小于.
    + 空集归谬.
    + apply 小于等于即小于后继...
      apply 后继除去 in 小于 as [].
      * left. apply 归纳假设...
      * subst...
  - apply 小于等于即小于后继 in 小于 as []...
    + apply 自然数是传递集 with n⁺...
    + subst...
Qed.

(* 自然数的后继是大于该数的最小数 *)
Corollary 小于即后继小于等于 : ∀ n m ∈ ω, n ∈ m ↔ n⁺ ⋸ m.
Proof with auto.
  intros n Hn m Hm. split; intros 小于.
  - apply 后继保序 in 小于...
    apply 小于等于即小于后继 in 小于...
  - apply 小于等于即小于后继 in 小于...
    apply 后继保序...
Qed.

Theorem 小于的反自反性 : ∀n ∈ ω, n ∉ n.
Proof.
  intros n Hn. 归纳 n; intros 反设.
  空集归谬. apply 归纳假设. apply 后继保序; auto.
Qed.

Corollary 小于则不等 : ∀m ∈ ω, ∀n ∈ m, n ≠ m.
Proof.
  intros m Hm n 小于 相等. subst.
  eapply 小于的反自反性; eauto.
Qed.

Corollary 自然数不等于其后继 : ∀n ∈ ω, n ≠ n⁺.
Proof. intros n Hn. apply 小于则不等; auto. Qed. 

Corollary ω不等于自然数 : ∀n ∈ ω, ω ≠ n.
Proof.
  intros n Hn 相等.
  apply (小于的反自反性 n); auto. congruence.
Qed.
Global Hint Resolve ω不等于自然数 : core.

Theorem 小于的传递性 : ∀n ∈ ω, ∀ k m, k ∈ m → m ∈ n → k ∈ n.
Proof. exact 自然数是传递集. Qed.

Theorem 小于的连通性 : ∀ n m ∈ ω, n ≠ m → n ∈ m ∨ m ∈ n.
Proof with auto.
  intros n Hn.
  归纳 n; intros k Hk 不等.
  - assert (k ≠ ∅) by congruence.
    apply 非零自然数的前驱存在 in H as [p [Hp Heq]]...
    left. subst...
  - 讨论 k.
    + right...
    + assert (m ≠ k) by congruence.
      apply 归纳假设 in H as []...
      * left. apply 后继保序 in H...
      * right. apply 后继保序 in H...
Qed.

Corollary 小于的完全性 : ∀ n m ∈ ω, n ⋸ m ∨ m ⋸ n.
Proof with auto.
  intros n Hn m Hm. 排中 (m = n).
  - left. right...
  - apply 小于的连通性 in H as []...
Qed.

Corollary 不为零即大于零 : ∀n ∈ ω, n ≠ ∅ ↔ ∅ ∈ n.
Proof with auto.
  intros n Hn. split; intros.
  - apply 小于的连通性 in H as []... 空集归谬.
  - 讨论 n... 空集归谬.
Qed.

Corollary 小于即真包含 : ∀ n m ∈ ω, n ∈ m ↔ n ⊂ m.
Proof with auto.
  intros n Hn m Hm. split.
  - intros 小于. split.
    + apply 传递集即其元素都为其子集...
    + apply 小于则不等...
  - intros [包含 不等].
    apply 小于的连通性 in 不等 as []...
    apply 包含 in H. exfalso. apply (小于的反自反性 m)...
Qed.

Corollary 小于即不是父集 : ∀ n m ∈ ω, n ∈ m ↔ m ⊈ n.
Proof with eauto.
  intros n Hn m Hm. split.
  - intros 小于 父集.
    apply 父集 in 小于. apply (小于的反自反性 n)...
  - intros 不是父集.
    排中 (m = n) as [相等|不等].
    + exfalso. apply 不是父集. subst...
    + apply 小于的连通性 in 不等 as [|]...
      exfalso. apply 不是父集. apply 小于即真包含...
Qed.

Corollary 小于等于即包含 : ∀ n m ∈ ω, n ⋸ m ↔ n ⊆ m.
Proof with eauto.
  intros n Hn m Hm. split.
  - intros [小于|等于].
    + apply 传递集即其元素都为其子集...
    + subst...
  - intros 包含.
    排中 (m = n) as [相等|不等]. right...
    left. apply 小于的连通性 in 不等 as []...
    apply 包含 in H. exfalso. apply (小于的反自反性 m)...
Qed.

Corollary 包含即小于后继 : ∀ n m ∈ ω, n ⊆ m ↔ n ∈ m⁺.
Proof with auto.
  intros n Hn m Hm.
  rewrite <- 小于等于即小于后继...
  symmetry. apply 小于等于即包含... 
Qed.

Corollary 小于等于即不大于 : ∀ n m ∈ ω, n ⋸ m ↔ m ∉ n.
Proof with auto.
  intros n Hn m Hm. rewrite 小于等于即包含... split.
  - intros 包含 大于. apply 小于即不是父集 in 大于...
  - intros 不大于. 反证. apply 小于即不是父集 in 反设...
Qed.
