(** Coq coding by choukh, Oct 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Axiom.Extensionality.
Require Import BBST.Axiom.Separation.
Require Import BBST.Definition.Complement.
Require Import BBST.Definition.Singleton.
Require Import BBST.Definition.Function.
Require Import BBST.Definition.Omega.
Require Import BBST.Definition.OmegaRecursion.
Require Import BBST.Definition.NatEmbedding.
Require Import BBST.Lemma.MetaFunction.

Local Coercion 自动嵌入 := λ n, 嵌入 n.

Declare Scope 自然数算术域.
Open Scope 自然数算术域.

Definition σ := 函数 ω ω 后继.

Lemma σ为映射 : σ : ω ⇒ ω.
Proof. apply 元映射, ω归纳. Qed.
Local Hint Resolve σ为映射 : core.

Lemma σ应用 : ∀n ∈ ω, σ[n] = n⁺.
Proof. intros n Hn. apply 元应用; auto. Qed.

Fact σ为双射 : σ : ω ⟺ ω - {∅,}.
Proof with auto.
  apply 双射即单源射满的映射. split3.
  - split. apply σ为映射. split. apply σ为映射.
    intros y Hy. 值|-Hy as [x Hp]. 关系|-Hp. subst.
    apply 分离介入... apply 单集外介入...
  - intros x y z Hxz Hyz. 关系|-Hxz. 关系|-Hyz. subst.
    apply 后继是单射 in Hyz...
  - intros y Hy. apply 分离除去 in Hy as [Hy Hy']. apply 单集外除去 in Hy'.
    apply 非零自然数的前驱存在 in Hy' as [k [Hk Heq]]...
    exists k. split... rewrite σ应用...
Qed.

Definition 加于 := λ n, ω递归函数 σ ω n.
Definition 加法 := λ n m, (加于 n)[m].
Notation "n + m" := (加法 n m) : 自然数算术域.

Lemma 加于为映射 : ∀n ∈ ω, 加于 n : ω ⇒ ω.
Proof. intros n Hn. apply ω递归定理; auto. Qed.
Local Hint Immediate 加于为映射 : core.

Lemma 加法对ω封闭 : ∀ n m ∈ ω, n + m ∈ ω.
Proof. intros. apply 映射除去 with ω; auto. Qed.
Global Hint Resolve 加法对ω封闭 : core.

Theorem 加零 : ∀n ∈ ω, n + 0 = n.
Proof. intros n Hn. apply ω递归定理; auto. Qed.

Theorem 加后继 : ∀ n m ∈ ω, n + m⁺ = (n + m)⁺.
Proof with auto.
  intros n Hn m Hm.
  pose proof (ω递归定理 σ ω n σ为映射 Hn) as [映 [_ 后继处]].
  fold (加于 n) in *. copy 映 as [函 [定 值]].
  apply 函数应用... 函数 -|. rewrite 定...
  rewrite 后继处, σ应用... eapply 映射除去 with ω...
Qed.

Example 一加一等于二 : 1 + 1 = 2.
Proof. simpl. rewrite 加后继, 加零; auto. Qed.

Definition 乘于 := λ n, ω递归函数 (加于 n) ω 0.
Definition 乘法 := λ n m, (乘于 n)[m].
Notation "n * m" := (乘法 n m) : 自然数算术域.

Lemma 乘于为映射 : ∀n ∈ ω, 乘于 n : ω ⇒ ω.
Proof. intros n Hn. apply ω递归定理; auto. Qed.
Local Hint Immediate 乘于为映射 : core.

Lemma 乘法对ω封闭 : ∀ n m ∈ ω, n * m ∈ ω.
Proof. intros. apply 映射除去 with ω; auto. Qed.
Global Hint Resolve 乘法对ω封闭 : core.

Theorem 乘零 : ∀n ∈ ω, n * 0 = 0.
Proof. intros n Hn. apply ω递归定理; auto. Qed.

Theorem 乘后继 : ∀ n m ∈ ω, n * m⁺ = n + n * m.
Proof with auto.
  intros n Hn m Hm.
  pose proof (ω递归定理 (加于 n) ω 0) as [映 [_ 后继处]]...
  fold (乘于 n) in *. copy 映 as [函 [定 值]].
  apply 函数应用... 函数 -|. rewrite 定... rewrite 后继处...
Qed.

Definition 设底数 := λ n, ω递归函数 (乘于 n) ω 1.
Definition 幂运算 := λ n m, (设底数 n)[m].
Notation "n ^ m" := (幂运算 n m) : 自然数算术域.

Lemma 设底数为映射 : ∀n ∈ ω, 设底数 n : ω ⇒ ω.
Proof. intros n Hn. apply ω递归定理; auto. Qed.
Local Hint Immediate 设底数为映射 : core.

Lemma 幂运算对ω封闭 : ∀ n m ∈ ω, n ^ m ∈ ω.
Proof. intros. apply 映射除去 with ω; auto. Qed.
Global Hint Resolve 幂运算对ω封闭 : core.

Theorem 零次幂 : ∀n ∈ ω, n ^ 0 = 1.
Proof. intros n Hn. apply ω递归定理; auto. Qed.

Theorem 后继次幂 : ∀ n m ∈ ω, n ^ m⁺ = n * n ^ m.
Proof with auto.
  intros n Hn m Hm.
  pose proof (ω递归定理 (乘于 n) ω 1) as [映 [_ 后继处]]...
  fold (设底数 n) in *. copy 映 as [函 [定 值]].
  apply 函数应用... 函数 -|. rewrite 定... rewrite 后继处...
Qed.

Lemma 加一 : ∀n ∈ ω, n + 1 = n⁺.
Proof. intros n Hn. simpl. rewrite 加后继, 加零; auto. Qed.

Lemma 乘一 : ∀n ∈ ω, n * 1 = n.
Proof. intros n Hn. simpl. rewrite 乘后继, 乘零, 加零; auto. Qed.

Lemma 一次幂 : ∀n ∈ ω, n ^ 1 = n.
Proof. intros n Hn. simpl. rewrite 后继次幂, 零次幂, 乘一; auto. Qed.

Theorem 加法结合律 : ∀ n m p ∈ ω, (n + m) + p = n + (m + p).
Proof with auto.
  intros n Hn m Hm p Hp. 归纳 p.
  - repeat rewrite 加零...
  - repeat rewrite 加后继... rewrite 归纳假设...
Qed.

Lemma 加于零 : ∀n ∈ ω, 0 + n = n.
Proof.
  intros n Hn. 归纳 n. apply 加零; auto.
  rewrite 加后继, 归纳假设; auto.
Qed.

Lemma 加于后继 : ∀ n m ∈ ω, n⁺ + m = (n + m)⁺.
Proof with auto.
  intros n Hn m Hm. 归纳 m.
  - repeat rewrite 加零...
  - repeat rewrite 加后继... rewrite 归纳假设...
Qed.

Theorem 加法交换律 : ∀ n m ∈ ω, n + m = m + n.
Proof with auto.
  intros n Hn m Hm. 讨论 n.
  - rewrite 加零, 加于零...
  - 归纳 m.
    + rewrite 加零, 加于零...
    + rewrite 加后继, 归纳假设, 加于后继...
Qed.

Corollary 加于一 : ∀n ∈ ω, 1 + n = n⁺.
Proof. intros n Hn. rewrite 加法交换律, 加一; auto. Qed.

Theorem 乘法分配律 : ∀ n m p ∈ ω, n * (m + p) = n * m + n * p.
Proof with auto.
  intros n Hn m Hm p Hp. 归纳 p.
  - rewrite 加零, 乘零, 加零...
  - rewrite 加后继, 乘后继, 乘后继, 归纳假设...
    rewrite <- 加法结合律, <- 加法结合律, (加法交换律 n)...
Qed.

Theorem 乘法结合律 : ∀ n m p ∈ ω, (n * m) * p = n * (m * p).
Proof with auto.
  intros n Hn m Hm p Hp. 归纳 p.
  - repeat rewrite 乘零...
  - repeat rewrite 乘后继... rewrite 乘法分配律, 归纳假设...
Qed.

Lemma 乘于零 : ∀n ∈ ω, 0 * n = 0.
Proof with auto.
  intros n Hn. 归纳 n. rewrite 乘零...
  rewrite 乘后继, 归纳假设, 加零...
Qed.

Lemma 乘于后继 : ∀ n m ∈ ω, n⁺ * m = m + (n * m).
Proof with auto.
  intros n Hn m Hm.  归纳 m.
  - repeat rewrite 乘零... rewrite 加零...
  - repeat rewrite 乘后继, 加于后继... rewrite 归纳假设...
    repeat rewrite <- 加法结合律... rewrite (加法交换律 n)...
Qed.

Theorem 乘法交换律 : ∀ n m ∈ ω, n * m = m * n.
Proof with auto.
  intros n Hn m Hm. 讨论 n.
  - rewrite 乘零, 乘于零...
  - 归纳 m.
    + rewrite 乘零, 乘于零...
    + repeat rewrite 乘后继, 加于后继...
      rewrite 归纳假设, 乘后继, 乘于后继...
      repeat rewrite <- 加法结合律... rewrite (加法交换律 n)...
Qed.

Corollary 乘于一 : ∀n ∈ ω, 1 * n = n.
Proof. intros n Hn. rewrite 乘法交换律, 乘一; auto. Qed.

Corollary 左侧乘法分配律 : ∀ n m p ∈ ω, (n + m) * p = n * p + m * p.
Proof.
  intros n Hn m Hm p Hp.
  rewrite 乘法交换律, 乘法分配律, 乘法交换律, (乘法交换律 p); auto.
Qed.

Theorem 底数为零的幂 : ∀n ∈ ω, n ≠ 0 → 0 ^ n = 0.
Proof with auto.
  intros n Hn H. 讨论 n. exfalso...
  rewrite 后继次幂, 乘于零...
Qed.

Theorem 底数为一的幂 : ∀ n ∈ ω, 1 ^ n = 1.
Proof with auto.
  intros n Hn. 归纳 n.
  - apply 零次幂...
  - rewrite 后继次幂, 归纳假设, 乘于一...
Qed.

Theorem 底数分配律 : ∀ n m p ∈ ω, (n * m) ^ p = n ^ p * m ^ p.
Proof with auto.
  intros n Hn m Hm p Hp. 归纳 p.
  - repeat rewrite 零次幂... rewrite 乘一...
  - repeat rewrite 后继次幂... rewrite 归纳假设.
    rewrite 乘法结合律, <- (乘法结合律 m), (乘法交换律 m), 乘法结合律, <- 乘法结合律...
Qed.

Theorem 指数和运算律 : ∀ n m p ∈ ω, n ^ (m + p) = n ^ m * n ^ p.
Proof with auto.
  intros n Hn m Hm p Hp. 归纳 p.
  - rewrite 加零, 零次幂, 乘一...
  - rewrite 加后继, 后继次幂, 后继次幂, 归纳假设...
    repeat rewrite <- 乘法结合律... rewrite (乘法交换律 n)...
Qed.

Theorem 指数积运算律 : ∀ n m p ∈ ω, n ^ (m * p) = (n ^ m) ^ p.
Proof with auto.
  intros n Hn m Hm p Hp. 归纳 p.
  - rewrite 乘零, 零次幂, 零次幂...
  - rewrite 后继次幂, 乘后继, 指数和运算律, 归纳假设...
Qed.
