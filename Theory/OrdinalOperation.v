(** Coq coding by choukh, Oct 2021 **)

Require Import BBST.Theory.Ordinal.
Local Hint Resolve 𝐎𝐍为传递类 : core.

Notation 为序数运算 F := (∀α ⋵ 𝐎𝐍, F α ⋵ 𝐎𝐍).

Definition 单调递增 := λ F, ∀α ⋵ 𝐎𝐍, ∀β ∈ α, F β ∈ F α.

Definition 极限处连续 := λ F, ∀α ⋵ 𝐋𝐈𝐌, α ≠ ∅ → F α = sup{F β | β ∊ α}.

Definition 为序数嵌入 := λ F, 为序数运算 F ∧ 单调递增 F ∧ 极限处连续 F.

Definition 后继处递增 := λ F, ∀α ⋵ 𝐎𝐍, F α ∈ F α⁺.

Definition 弱自增 := λ F, ∀α ⋵ 𝐎𝐍, α ⋸ F α.

Definition 对上确界封闭 := λ C, ∀ A, A ≠ ∅ → A ⪽ C → sup A ⋵ C.

Definition 有界 := λ C, ∃α ⋵ 𝐎𝐍, ∀β ⋵ C, β ⋸ α.

Definition 无界 := λ C, ∀α ⋵ 𝐎𝐍, ∃β ⋵ C, α ∈ β.

Theorem 后继处递增且极限处连续的序数运算单调递增 :
  ∀ F, 为序数运算 F → 后继处递增 F → 极限处连续 F → 单调递增 F.
Proof with auto.
  intros F 运算 后继 极限. unfold 单调递增.
  超限归纳. intros β 小于. 超限讨论 α.
  - 空集归谬.
  - apply 后继除去 in 小于 as [].
    apply 序数传递 with (F α)... subst...
  - rewrite (极限 α)... apply 集族并介入 with β⁺.
    apply 极限序数有其任意元素的后继... apply 后继. eauto.
Qed.

Section 序数递归.
Variable y₀ : 集合.
Variable F : 函数类型.

Local Definition G关系 := λ f y,
  (dom f = ∅ → y₀ = y) ∧ (dom f ≠ ∅ →
    (dom f ⋵ 𝐒𝐔𝐂 → F f[sup (dom f)] = y) ∧
    (dom f ⋵ 𝐋𝐈𝐌 → sup (ran f) = y)
  ).

Local Lemma G关系有函数性 : ∀ f, dom f ⋵ 𝐎𝐍 → ∃!y, G关系 f y.
Proof with auto; try easy.
  intros. 排中 (dom f = ∅).
  - exists y₀. split... intros y []...
  - destruct (序数要么为后继要么为极限 (dom f) H) as [后继|极限].
    + exists (F f[sup (dom f)]). split.
      * split... intros _. split... intros 极限.
        apply 序数为极限当且仅当它不为后继 in 极限...
      * intros y []. apply H2...
    + exists (sup (ran f)). split.
      * split... intros _. split... intros 后继.
        apply 序数为极限当且仅当它不为后继 in 极限...
      * intros y []. apply H2...
Qed.

Local Definition G := λ f, 描述 (G关系 f).

Local Lemma G规范 : ∀ f, dom f ⋵ 𝐎𝐍 → G关系 f (G f).
Proof. intros. unfold G. apply 描述公理. apply G关系有函数性. auto. Qed.

Definition 序数递归 := 超限递归 G.

Theorem 序数递归_0 : 序数递归 ∅ = y₀.
Proof with auto.
  intros. unfold 序数递归. rewrite 超限递归定理...
  symmetry. eapply G规范; rewrite 类函数限制之定义域...
Qed.

Theorem 序数递归_后继 : ∀α ⋵ 𝐎𝐍, 序数递归 α⁺ = F (序数递归 α).
Proof with auto.
  intros. unfold 序数递归. rewrite 超限递归定理...
  rewrite (类函数限制之应用 (超限递归 G) α⁺)...
  replace α with (sup (dom (超限递归 G ↑ α⁺))) at 3.
  symmetry. apply G规范. 1-4: rewrite 类函数限制之定义域...
  exists α... apply 后继序数的上确界为前驱...
Qed.

Theorem 序数递归_极限 : 极限处连续 序数递归.
Proof with auto.
  intros α 极限 缺零. copy 极限 as [Hα Hsup].
  unfold 序数递归. rewrite 超限递归定理, <- 类函数限制之值域...
  symmetry. apply G规范; rewrite 类函数限制之定义域...
Qed.

End 序数递归.

Theorem 序数运算的递归为序数运算 : ∀y₀ ⋵ 𝐎𝐍, ∀ F, 为序数运算 F → 为序数运算 (序数递归 y₀ F).
Proof with auto.
  intros y₀ Hy₀ F H. 超限归纳. 超限讨论 α.
  - rewrite 序数递归_0...
  - rewrite 序数递归_后继...
  - rewrite 序数递归_极限...
    apply 序数集的并是序数. intros x Hx.
    apply 替代除去 in Hx as [β [Hβ Hx]]. subst. apply 归纳假设...
Qed.

Lemma 后继处递增的序数递归单调递增 : ∀y₀ ⋵ 𝐎𝐍, ∀ F, 为序数运算 F → 
  后继处递增 (序数递归 y₀ F) → 单调递增 (序数递归 y₀ F).
Proof with auto.
  intros y₀ Hy₀ F 运算 递增.
  apply 后继处递增且极限处连续的序数运算单调递增...
  apply 序数运算的递归为序数运算... apply 序数递归_极限.
Qed.

Theorem 后继处递增的序数递归是序数嵌入 : ∀y₀ ⋵ 𝐎𝐍, ∀ F, 为序数运算 F → 
  后继处递增 (序数递归 y₀ F) → 为序数嵌入 (序数递归 y₀ F).
Proof with auto.
  intros. split3. apply 序数运算的递归为序数运算...
  apply 后继处递增的序数递归单调递增... apply 序数递归_极限.
Qed.

Section 缺零递归.
Variable y₀ : 集合.
Variable F : 函数类型.

Local Definition 缺零G关系 := λ f y,
  (dom f = ∅ → y₀ = y) ∧ (dom f ≠ ∅ →
    (dom f ⋵ 𝐒𝐔𝐂 → F f[sup (dom f)] = y) ∧
    (dom f ⋵ 𝐋𝐈𝐌 → sup (ran (f ↾ (dom f - {∅,}))) = y)
  ).

Local Lemma 缺零G关系有函数性 : ∀ f, dom f ⋵ 𝐎𝐍 → ∃!y, 缺零G关系 f y.
Proof with auto; try easy.
  intros. 排中 (dom f = ∅).
  - exists y₀. split... intros y []...
  - destruct (序数要么为后继要么为极限 (dom f) H) as [后继|极限].
    + exists (F f[sup (dom f)]). split.
      * split... intros _. split... intros 极限.
        apply 序数为极限当且仅当它不为后继 in 极限...
      * intros y []. apply H2...
    + exists (sup (ran (f ↾ (dom f - {∅,})))). split.
      * split... intros _. split... intros 后继.
        apply 序数为极限当且仅当它不为后继 in 极限...
      * intros y []. apply H2...
Qed.

Local Definition 缺零G := λ f, 描述 (缺零G关系 f).

Local Lemma 缺零G规范 : ∀ f, dom f ⋵ 𝐎𝐍 → 缺零G关系 f (缺零G f).
Proof. intros. unfold 缺零G. apply 描述公理. apply 缺零G关系有函数性. auto. Qed.

Definition 缺零递归 := 超限递归 缺零G.

Theorem 缺零递归_0 : 缺零递归 ∅ = y₀.
Proof with auto.
  intros. unfold 缺零递归. rewrite 超限递归定理...
  symmetry. eapply 缺零G规范; rewrite 类函数限制之定义域...
Qed.

Theorem 缺零递归_后继 : ∀α ⋵ 𝐎𝐍, 缺零递归 α⁺ = F (缺零递归 α).
Proof with auto.
  intros. unfold 缺零递归. rewrite 超限递归定理...
  rewrite (类函数限制之应用 (超限递归 缺零G) α⁺)...
  replace α with (sup (dom (超限递归 缺零G ↑ α⁺))) at 3.
  symmetry. apply 缺零G规范. 1-4: rewrite 类函数限制之定义域...
  exists α... apply 后继序数的上确界为前驱...
Qed.

Theorem 缺零递归_极限 : ∀α ⋵ 𝐋𝐈𝐌, α ≠ ∅ → 缺零递归 α = sup{缺零递归 β | β ∊ α - {∅,}}.
Proof with auto.
  intros α 极限 缺零. copy 极限 as [Hα Hsup].
  unfold 缺零递归. rewrite 超限递归定理, <- 类函数限制之值域...
  set (超限递归 缺零G ↑ α) as f.
  replace (超限递归 缺零G ↑ α - {∅,}) with (f ↾ (dom f - {∅,})).
  - symmetry. apply 缺零G规范; unfold f; rewrite 类函数限制之定义域...
  - unfold f. rewrite 类函数限制之定义域. apply 类函数限制到父再子...
Qed.

End 缺零递归.

Theorem 序数运算的缺零递归为序数运算 : ∀y₀ ⋵ 𝐎𝐍, ∀ F, 为序数运算 F → 为序数运算 (缺零递归 y₀ F).
Proof with auto.
  intros y₀ Hy₀ F H. 超限归纳. 超限讨论 α.
  - rewrite 缺零递归_0...
  - rewrite 缺零递归_后继...
  - rewrite 缺零递归_极限...
    apply 序数集的并是序数. intros x Hx. apply 替代除去 in Hx as [β [Hβ Hx]].
    apply 分离之父集 in Hβ. subst. apply 归纳假设...
Qed.
