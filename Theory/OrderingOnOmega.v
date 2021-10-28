(** Coq coding by choukh, Oct 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Axiom.Separation.
Require Import BBST.Definition.Complement.
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
  intros n Hn m Hm. split.
  - 归纳 m; intros 小于.
    + 空集归谬.
    + apply 小于等于即小于后继...
      apply 后继除去 in 小于 as [].
      * left. apply 归纳假设...
      * subst...
  - intros 小于. apply 小于等于即小于后继 in 小于 as []...
    + apply 自然数为传递集 with n⁺...
    + subst...
Qed.

(* n⁺是大于n的最小数 *)
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
  归纳; intros 反设.
  空集归谬. apply 归纳假设. apply 后继保序; auto.
Qed.
Global Hint Resolve 小于的反自反性 : core.

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

Theorem 小于的传递性 : ∀n ∈ ω, ∀ k m, k ∈ m → m ∈ n → k ∈ n.
Proof. exact 自然数为传递集. Qed.

Theorem 小于的三歧性 : ∀ n m ∈ ω, n = m ∨ n ∈ m ∨ m ∈ n.
Proof with auto.
  归纳; intros m Hm.
  - 排中 (m = ∅)... apply 非零自然数的前驱存在 in H as [p [Hp Heq]]...
    right. left. subst...
  - 讨论 m. right. right...
    destruct (归纳假设 m Hp) as [|[]].
    + left. subst...
    + right. left. apply 后继保序 in H...
    + right. right. apply 后继保序 in H...
Qed.

Corollary 不为零即大于零 : ∀n ∈ ω, n ≠ ∅ ↔ ∅ ∈ n.
Proof with auto.
  intros n Hn. split; intros.
  - destruct (小于的三歧性 n Hn ∅) as [|[]]... exfalso... 空集归谬.
  - 讨论 n... 空集归谬.
Qed.

Theorem 小于即真包含 : ∀ n m ∈ ω, n ∈ m ↔ n ⊂ m.
Proof with auto.
  intros n Hn m Hm. split.
  - intros 小于. split.
    + apply 传递集即其元素都为其子集...
    + apply 小于则不等...
  - intros [包含 不等].
    destruct (小于的三歧性 n Hn m Hm) as [|[]]... exfalso...
    apply 包含 in H. exfalso. apply (小于的反自反性 m)...
Qed.

Theorem 小于等于即包含 : ∀ n m ∈ ω, n ⋸ m ↔ n ⊆ m.
Proof with auto.
  intros n Hn m Hm. split.
  - intros [小于|等于].
    + apply 传递集即其元素都为其子集...
    + subst...
  - intros 包含. destruct (小于的三歧性 n Hn m Hm) as [|[]]...
    apply 包含 in H. exfalso. apply (小于的反自反性 m)...
Qed.

Corollary 包含即小于后继 : ∀ n m ∈ ω, n ⊆ m ↔ n ∈ m⁺.
Proof with auto.
  intros n Hn m Hm.
  rewrite <- 小于等于即小于后继...
  symmetry. apply 小于等于即包含...
Qed.

Lemma ω是ϵ反自反 : ϵ反自反 ω.
Proof. exact 小于的反自反性. Qed.

Lemma ω是ϵ传递 : ϵ传递 ω.
Proof. firstorder using 小于的传递性. Qed.

Lemma ω是ϵ三歧 : ϵ三歧 ω.
Proof. exact 小于的三歧性. Qed.

Theorem ω是ϵ全序 : ϵ全序 ω.
Proof.
  repeat split. apply ω是ϵ反自反. apply ω是ϵ传递. apply ω是ϵ三歧.
Qed.
Global Hint Resolve ω是ϵ全序 : core. 

Corollary ω的任意子集是ϵ全序 : ∀ N, N ⊆ ω → ϵ全序 N.
Proof. intros. apply ϵ全序集的任意子集是ϵ全序 with ω; auto. Qed.
Global Hint Resolve ω的任意子集是ϵ全序 : core.

(* 练习7-1 *)
(* ω的任意非空子集有最小数 *)
Theorem ω是ϵ良基 : ϵ良基 ω.
Proof with auto.
  intros N 非空 子集. 反证.
  rewrite ϵ全序则无ϵ最小元即总有ϵ更小 in 反设...
  cut (∀n ∈ ω, n ∉ N). firstorder using 非空介入.
  cut (∀n ∈ ω, ∀k ∈ n, k ∉ N). firstorder.
  归纳; intros k Hkn. 空集归谬.
  intros HkN. destruct (反设 k HkN) as [x [HxN Hxk]].
  apply 归纳假设 with x... eapply 包含即小于后继 with k...
Qed.

Theorem ω是ϵ良序 : ϵ良序 ω.
Proof. split. apply ω是ϵ全序. apply ω是ϵ良基. Qed.
Global Hint Resolve ω是ϵ良序 : core.

Corollary ω的任意子集是ϵ良序 : ∀ N, N ⊆ ω → ϵ良序 N.
Proof. intros. apply ϵ良序集的任意子集是ϵ良序 with ω; auto. Qed.

Corollary 自然数是ϵ良序 : ∀n ∈ ω, ϵ良序 n.
Proof. intros. apply ω的任意子集是ϵ良序, 传递集即其元素都为其子集; auto. Qed.

Theorem 强归纳原理 : ∀ N, N ⊆ ω → (∀n ∈ ω, n ⊆ N → n ∈ N) → N = ω.
Proof with auto.
  intros N 子集 强归纳. 反证.
  pose proof (ω是ϵ良基 (ω - N)) as [m [Hm 最小]].
  - intros 空. rewrite <- 包含即补集为空 in 空.
    apply 反设. apply 包含的反对称性...
  - intros x Hx. now apply 分离之父集 in Hx.
  - apply 分离除去 in Hm as [Hm Hm'].
    apply Hm'. apply 强归纳... intros n Hnm.
    assert (Hn: n ∈ ω). apply ω为传递集 with m...
    反证. apply ϵ全序则ϵ可换 with ω n m...
    apply 最小. apply 分离介入...
Qed.

Corollary 强归纳法 : ∀ P : 性质, (∀n ∈ ω, ((∀m ∈ n, P m) → P n)) → ∀n ∈ ω, P n.
Proof with auto.
  intros P 强归纳 n Hn. set {n ∊ ω | P n} as N.
  assert (N = ω). {
    apply 强归纳原理. apply 分离为子集.
    intros m Hm 归纳假设. apply 分离介入... apply 强归纳...
    intros k Hk. apply 归纳假设 in Hk. apply 分离之条件 in Hk...
  }
  rewrite <- H in Hn. apply 分离之条件 in Hn...
Qed.

Ltac 强归纳 n Hn :=
  match goal with
    | |- ∀n ∈ ω, _ => intros n Hn; pattern n
    | Hn: n ∈ ω |- _ => pattern n
  end;
  match goal with |- ?P n => let IH := fresh "归纳假设" in
    generalize dependent n; apply (强归纳法 P); intros n Hn IH
  end.

Tactic Notation "强归纳" simple_intropattern(n) simple_intropattern(Hn) := 强归纳 n Hn.
Tactic Notation "强归纳" simple_intropattern(n) := 强归纳 n ?Hn.
Tactic Notation "强归纳" := let n := fresh "n" in let Hn := fresh "Hn" in 强归纳 n Hn.

Theorem 强归纳原理' : ∀ N, N ⊆ ω → 总有ϵ更小 N → N = ∅.
Proof.
  intros N 子集 总有更小. 反证.
  pose proof (ω是ϵ良基 N 反设 子集).
  apply ϵ全序则无ϵ最小元即总有ϵ更小 with N; auto.
Qed.

Corollary 强归纳法' : ∀ P : 性质, P ∅ → (∀n ∈ ω, ¬ P n⁺ → ¬ P n) → ∀n ∈ ω, P n.
Proof with auto.
  intros P 起始 归纳 n Hn. set {n ∊ ω | ¬ P n} as N.
  assert (N = ∅). {
    apply 强归纳原理'. apply 分离为子集.
    intros m Hm. apply 分离除去 in Hm as [Hm 归纳假设].
    讨论 m. exfalso. apply 归纳假设...
    exists m. split... apply 分离介入...
  }
  反证. apply 空集除去 with N n... apply 分离介入...
Qed.

Ltac 强归纳_反证 n Hn :=
  match goal with
    | |- ∀n ∈ ω, _ => intros n Hn; pattern n
    | Hn: n ∈ ω |- _ => pattern n
  end;
  match goal with |- ?P n => let IH := fresh "归纳假设" in
    generalize dependent n; apply (强归纳法' P); [|intros n Hn IH]
  end.

Tactic Notation "强归纳_反证" simple_intropattern(n) simple_intropattern(Hn) := 强归纳_反证 n Hn.
Tactic Notation "强归纳_反证" simple_intropattern(n) := 强归纳_反证 n ?Hn.
Tactic Notation "强归纳_反证" := let n := fresh "n" in let Hn := fresh "Hn" in 强归纳_反证 n Hn.
