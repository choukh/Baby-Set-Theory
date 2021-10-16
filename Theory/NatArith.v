(** Coq coding by choukh, Oct 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Axiom.Extensionality.
Require Import BBST.Axiom.Separation.
Require Import BBST.Definition.Complement.
Require Import BBST.Definition.Singleton.
Require Import BBST.Definition.Omega.
Require Import BBST.Definition.Function.
Require Import BBST.Lemma.MetaFunction.

Definition σ := 函数 ω ω 后继.

Lemma σ为映射 : σ : ω ⇒ ω.
Proof. apply 元映射, ω归纳. Qed.

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
