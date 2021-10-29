(** Coq coding by choukh, Oct 2021 **)

Require Export BBST.Theory.Ordinal.

Definition 为序数运算 := λ F, ∀x ⋵ 𝐎𝐍, F x ⋵ 𝐎𝐍.

Section 递归运算.
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

Definition 递归运算 := 超限递归 G.

Theorem 递归运算_0 : 递归运算 ∅ = y₀.
Proof with auto.
  intros. unfold 递归运算. rewrite 超限递归定理...
  symmetry. eapply G规范. 1-2: rewrite 类函数限制之定义域...
Qed.

Theorem 递归运算_后继 : ∀α ⋵ 𝐎𝐍, 递归运算 α⁺ = F (递归运算 α).
Proof with auto.
  intros. unfold 递归运算. rewrite 超限递归定理...
  rewrite (类函数限制之应用 (超限递归 G) α⁺)...
  replace α with (sup (dom (超限递归 G ↑ α⁺))) at 3.
  symmetry. apply G规范. 1-4: rewrite 类函数限制之定义域...
  exists α... apply 后继序数的上确界为前驱...
Qed.

Theorem 递归运算_极限 : ∀α ⋵ 𝐋𝐈𝐌, α ≠ ∅ → 递归运算 α = sup{递归运算 β | β ∊ α}.
Proof with auto.
  intros α 极限 非零. copy 极限 as [Hα Hsup].
  unfold 递归运算. rewrite 超限递归定理, <- 类函数限制之值域...
  symmetry. apply G规范. 1-3: rewrite 类函数限制之定义域...
Qed.

End 递归运算.

Lemma 递归运算为序数运算 : ∀y₀ ⋵ 𝐎𝐍, ∀ F, 为序数运算 F → 为序数运算 (递归运算 y₀ F).
Proof with auto.
  intros y₀ Hy₀ F H. unfold 为序数运算.
  超限归纳. 超限讨论 α.
  - subst. rewrite 递归运算_0...
  - 后继序数. rewrite 递归运算_后继...
  - rewrite 递归运算_极限...
    apply 序数集的并是序数. intros x Hx.
    apply 替代除去 in Hx as [β [Hβ Hx]]. subst. apply 归纳假设...
Qed.
