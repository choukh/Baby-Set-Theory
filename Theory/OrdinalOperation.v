(** Coq coding by choukh, Oct 2021 **)

Require Import BBST.Theory.Ordinal.
Local Hint Resolve 𝐎𝐍为传递类 : core.
Local Hint Immediate ω为序数集 : core.

Notation 有限递增 F := (∀n ∈ ω, F n ∈ F n⁺).
Notation 有限保序 F := (∀n ∈ ω, ∀m ∈ n, F m ∈ F n).

Notation 有限弱递增 F := (∀n ∈ ω, F n ⋸ F n⁺).
Notation 有限弱保序 F := (∀n ∈ ω, ∀m ∈ n, F m ⋸ F n).

Notation 为序数运算 F := (∀α ⋵ 𝐎𝐍, F α ⋵ 𝐎𝐍).
Notation 后继处递增 F := (∀α ⋵ 𝐎𝐍, F α ∈ F α⁺).
Notation 极限处连续 F := (∀α ⋵ 𝐋𝐈𝐌, α ≠ ∅ → F α = sup{F β | β ∊ α}).
Definition 为序数嵌入 := λ F, 为序数运算 F ∧ 后继处递增 F ∧ 极限处连续 F.

Definition 保序 := λ F, ∀α ⋵ 𝐎𝐍, ∀β ∈ α, F β ∈ F α.
Definition 双向保序 := λ F, ∀ α β ⋵ 𝐎𝐍, α ∈ β ↔ F α ∈ F β.
Definition 非无穷降链 := λ F, ∀α ⋵ 𝐎𝐍, α ⋸ F α.

Definition 对上确界封闭 := λ C, ∀ A, A ≠ ∅ → A ⪽ C → sup A ⋵ C.
Definition 有界 := λ C, ∃α ⋵ 𝐎𝐍, ∀β ⋵ C, β ⋸ α.
Definition 无界 := λ C, ∀α ⋵ 𝐎𝐍, ∃β ⋵ C, α ∈ β.

Theorem 序数嵌入保序 : ∀ F, 为序数嵌入 F → 保序 F.
Proof with auto.
  intros F [运算 [递增 连续]]. unfold 保序.
  超限归纳. intros β 小于. 超限讨论 α.
  - 空集归谬.
  - apply 后继除去 in 小于 as []. apply 序数传递 with (F α)... subst...
  - rewrite (连续 α)... apply 集族并介入 with β⁺.
    apply 极限序数有其任意元素的后继... apply 递增. eauto.
Qed.

Theorem 保序运算双向保序 : ∀ F, 为序数运算 F → 保序 F → 双向保序 F.
Proof with auto.
  intros F HF 保序 α Hα β Hβ. split...
  intros Hlt. destruct (序数三歧 α Hα β Hβ) as [|[]]...
  - exfalso. subst. apply 序数反自反 with (F β)...
  - exfalso. apply 保序 in H... apply 序数可换 in H...
Qed.

Corollary 序数嵌入双向保序 : ∀ F, 为序数嵌入 F → 双向保序 F.
Proof. intros. apply 保序运算双向保序. apply H. apply 序数嵌入保序, H. Qed.

Theorem 保序运算非无穷降链 : ∀ F, 为序数运算 F → 保序 F → 非无穷降链 F.
Proof with auto.
  intros F 运算 保序 α Hα. 反证. apply 序数可换 in 反设...
  generalize dependent α. 超限归纳. intros Hlt. apply 归纳假设 with (F α)...
Qed.

Corollary 序数嵌入非无穷降链 : ∀ F, 为序数嵌入 F → 非无穷降链 F.
Proof. intros. apply 保序运算非无穷降链. apply H. apply 序数嵌入保序, H. Qed.

Theorem 保序运算为类单射 : ∀ F, 为序数运算 F → 保序 F → 为类单射 𝐎𝐍 F.
Proof with auto.
  intros F 运算 保序 α Hα β Hβ 相等.
  destruct (序数三歧 α Hα β Hβ) as [|[]]; auto; exfalso; apply 保序 in H...
  apply 小于则不等 with (F β) (F α)...
  apply 小于则不等 with (F α) (F β)...
Qed.

Corollary 序数嵌入为类单射 : ∀ F, 为序数嵌入 F → 为类单射 𝐎𝐍 F.
Proof. intros. apply 保序运算为类单射. apply H. apply 序数嵌入保序, H. Qed.

Theorem 序数嵌入在极限处的值为极限 : ∀ F, 为序数嵌入 F → ∀α ⋵ 𝐋𝐈𝐌, α ≠ ∅ → F α ⋵ 𝐋𝐈𝐌.
Proof with auto.
  intros F [运算 [递增 连续]] α 极限 H0. copy 极限 as [Hα _].
  rewrite 连续... split.
  - apply 序数集的并为序数. intros y Hy.
    apply 替代除去 in Hy as [ξ [Hξ HFξ]]. subst y. apply 运算. eauto.
  - 外延 β Hβ.
    + apply 并集除去 in Hβ as [γ [Hγ Hβ]].
      apply 集族并除去 in Hγ as [ξ [Hξ HFξ]].
      apply 集族并介入 with ξ... apply 序数传递 with γ... apply 运算. eauto.
    + apply 集族并除去 in Hβ as [ξ [Hξ HFξ]]. apply 并集介入 with (F ξ)...
      apply 集族并介入 with ξ⁺... apply 极限序数有其任意元素的后继... apply 递增... eauto.
Qed.

Theorem 𝐎𝐍无界子类为真类 : ∀ C, C ⫃ 𝐎𝐍 → 无界 C → 为真类 C.
Proof.
  intros C 子类 无界 [A 为集合]. apply 𝐎𝐍为真类.
  exists (sup A). intros α Hα. apply 无界 in Hα as [β [Hβ Hα]].
  apply 并集介入 with β; auto.
Qed.

Theorem 上确界的嵌入等于嵌入集的上确界 : ∀ F, 为序数嵌入 F →
  ∀ A, A ≠ ∅ → A ⪽ 𝐎𝐍 → F (sup A) = sup {F α | α ∊ A}.
Proof with auto.
  intros F HF A H0 HA.
  assert (Hs: sup A ⋵ 𝐎𝐍). apply 序数集的并为序数...
  assert (HFs: F (sup A) ⋵ 𝐎𝐍). apply HF...
  assert (Hr: {F α | α ∊ A} ⪽ 𝐎𝐍). {
    intros x Hx. apply 替代除去 in Hx as [α [Hα H]]. subst x. apply HF...
  }
  assert (Hsr: sup {F α | α ∊ A} ⋵ 𝐎𝐍). apply 序数集的并为序数...
  apply 包含的反对称性.
  - remember (sup A) as σ. 超限讨论 σ.
    + apply 小于等于即包含... apply 序数集的并为上界... apply 替代介入_自动... rewrite H1. 
      apply 仅零或一之并为零 in H1 as []. exfalso... subst...
    + apply 小于等于即包含... apply 序数集的并为上界... apply 替代介入_自动.
      apply 为后继的上确界在序数集内... exists σ...
    + intros x Hx. copy HF as [_ [_ 连续]]. rewrite 连续 in Hx...
      apply 集族并除去 in Hx as [α [Hα Hx]]. rewrite Heqσ in Hα.
      apply 并集除去 in Hα as [β [Hβ Hα]]. apply 集族并介入 with β...
      apply 序数传递 with (F α)... apply 序数嵌入保序...
  - intros x Hx. apply 集族并除去 in Hx as [α [Hα Hx]].
    apply 序数集的并为上界 in HA as [_ Hle]. apply Hle in Hα as [].
    apply 序数传递 with (F α)... apply 序数嵌入保序... congruence.
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
    apply 序数集的并为序数. intros x Hx.
    apply 替代除去 in Hx as [β [Hβ Hx]]. subst. apply 归纳假设...
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
    apply 序数集的并为序数. intros x Hx. apply 替代除去 in Hx as [β [Hβ Hx]].
    apply 分离之父集 in Hβ. subst. apply 归纳假设...
Qed.

Module Import 无界子类元素的枚举.
Section 无界子类元素的枚举.
Variable C : 类.
Variable C为子类 : C ⫃ 𝐎𝐍.
Variable C无界 : 无界 C.

Local Definition G关系 := λ f y, y ⋵ C ∧ y ∉ ran f ∧ ∀x ⋵ C, x ∉ ran f → y ⋸ x.

Local Lemma G关系有函数性 : ∀ f, ∃! y, G关系 f y.
Proof with auto.
  intros. rewrite <- unique_existence. split.
  - assert (∃α ⋵ C, α ∉ ran f). {
      反证. apply 𝐎𝐍无界子类为真类 with C... exists (ran f)...
      intros α Hα. 反证. firstorder.
    }
    destruct H as [α Hα]. assert (Hαo: α ⋵ 𝐎𝐍). destruct Hα...
    set (λ β, β ⋵ C ∧ β ∉ ran f) as P.
    pose proof (存在满足条件的最小序数 α Hαo P Hα) as [μ [Hμo [Hμ Hle]]].
    destruct Hμ as [Hμ Hμ']. exists μ.
    split... split... intros x Hx Hx'. 排中 (x ⋸ α).
    + apply Hle... split...
    + apply 序数可换 in H... apply 序数传递_弱 with α...
  - intros x y [HxC [Hx H1]] [HyC [Hy H2]].
    apply H1 in Hy... apply H2 in Hx...
    destruct Hx; destruct Hy... exfalso. apply 序数可换 with x y...
Qed.
Local Hint Immediate G关系有函数性 : core.

Local Definition G := λ f, 描述 (G关系 f).

Local Lemma G规范 : ∀ f, dom f ⋵ 𝐎𝐍 → G关系 f (G f).
Proof. intros. unfold G. apply 描述公理. apply G关系有函数性. Qed.

Definition 枚举 := 超限递归 G.

(* 枚举是𝐎𝐍到其子类的映射 *)
Lemma 枚举规范甲 : ∀α ⋵ 𝐎𝐍, 枚举 α ⋵ C.
Proof with auto.
  intros. unfold 枚举. rewrite 超限递归定理...
  apply G规范. rewrite 类函数限制之定义域...
Qed.

Corollary 枚举为序数运算 : 为序数运算 枚举.
Proof. intros. apply C为子类, 枚举规范甲; auto. Qed.

(* 枚举元素与之前的元素都不同 *)
Lemma 枚举规范乙 : ∀α ⋵ 𝐎𝐍, ∀β ∈ α, 枚举 α ∉ {枚举 β | β ∊ α}.
Proof with auto.
  intros α Hα β Hβα. intros H. unfold 枚举 in H.
  rewrite 超限递归定理 in H... apply G规范 with (超限递归 G ↑ α).
  rewrite 类函数限制之定义域... rewrite 类函数限制之值域...
Qed.

(* 枚举元素是属于子类且与之前的元素都不同的最小序数 *)
Lemma 枚举规范丙 : ∀α ⋵ 𝐎𝐍, ∀ξ ⋵ C, ξ ∉ {枚举 β | β ∊ α} → 枚举 α ⋸ ξ.
Proof with auto.
  intros α Hα ξ Hξ H. unfold 枚举. rewrite 超限递归定理...
  apply G规范... rewrite 类函数限制之定义域... rewrite 类函数限制之值域...
Qed.

Theorem 枚举运算保序 : 保序 枚举.
Proof with auto.
  intros α Hα β Hβα. assert (Hβ: β ⋵ 𝐎𝐍). eauto.
  assert (枚举 α ∉ {枚举 γ | γ ∊ β}). {
    intros H. apply 替代除去 in H as [γ [Hγ H]].
    apply 枚举规范乙 with α β... apply 替代介入.
    exists γ. split... apply 序数传递 with β...
  }
  apply 枚举规范丙 in H as []... 2: apply 枚举规范甲...
  exfalso. apply 枚举规范乙 with α β... apply 替代介入. exists β...
Qed.

End 无界子类元素的枚举.
End 无界子类元素的枚举.

Section 任意不动点.
Variable F : 函数类型.
Variable F嵌入 : 为序数嵌入 F.
Variable α : 集合.
Variable Hα : α ⋵ 𝐎𝐍.

Local Notation G := (序数递归 α F).
Local Notation A := {G n | n ∊ ω}.
Definition 任意不动点 := sup A.
Local Notation β := 任意不动点.

Local Lemma A非空 : A ≠ ∅.
Proof. apply 非空除去. exists (G ∅). apply 替代介入_自动; auto. Qed.

Local Lemma A为序数集 : A ⪽ 𝐎𝐍.
Proof with auto.
  intros x Hx. apply 替代除去 in Hx as [n [Hn HGn]]. subst x.
  apply 序数运算的递归为序数运算... apply F嵌入.
Qed.

Local Lemma β为序数 : β ⋵ 𝐎𝐍.
Proof. apply 序数集的并为序数. apply A为序数集. Qed.

Local Lemma β任意大 : α ⋸ β.
Proof with auto.
  apply 序数集的并为上界. apply A为序数集.
  apply 替代介入. exists ∅. split... rewrite 序数递归_0...
Qed.

Local Lemma β为不动点 : F β = β.
Proof with auto.
  unfold β. rewrite (上确界的嵌入等于嵌入集的上确界 F F嵌入 A A非空 A为序数集). 外延.
  - apply 集族并除去 in H as [γ [Hγ H]].
    apply 替代除去 in Hγ as [n [Hn Hγ]]. subst.
    apply 并集介入 with (G n⁺). apply 替代介入_自动... rewrite 序数递归_后继...
  - apply 并集除去 in H as [γ [Hγ Hx]].
    apply 替代除去 in Hγ as [n [Hn Hγ]]. subst.
    apply 集族并介入 with (G n). apply 替代介入_自动... copy F嵌入 as [HF _].
    assert (G n ⋵ 𝐎𝐍). apply 序数运算的递归为序数运算...
    generalize dependent x. apply 小于等于即包含...
    apply 保序运算非无穷降链... apply 序数嵌入保序...
Qed.

Lemma 不动点为之 : β ⋵ 𝐎𝐍 ∧ F β = β ∧ α ⋸ β.
Proof. split3. apply β为序数. apply β为不动点. apply β任意大. Qed.

(* Veblen不动点定理：序数嵌入存在任意大的不动点 *)
Theorem 不动点定理 : ∃β ⋵ 𝐎𝐍, F β = β ∧ α ⋸ β.
Proof. exists β. apply 不动点为之. Qed.

End 任意不动点.

Section 最小不动点.
Variable F : 函数类型.
Variable F嵌入 : 为序数嵌入 F.

Local Notation β := (任意不动点 F ∅).

Definition 最小不动点 := inf {γ ∊ β⁺ | F γ = γ}.
Local Notation β₀ := 最小不动点.

Lemma 最小不动点为之 : β₀ ⋵ 𝐎𝐍 ∧ F β₀ = β₀ ∧ ∀γ ⋵ 𝐎𝐍, F γ = γ → β₀ ⋸ γ.
Proof. apply 满足条件的最小序数为之. apply β为序数; auto. apply β为不动点; auto. Qed.

Theorem 存在最小不动点 : ∃β ⋵ 𝐎𝐍, F β = β ∧ ∀γ ⋵ 𝐎𝐍, F γ = γ → β ⋸ γ.
Proof. exists β₀. apply 最小不动点为之. Qed.

End 最小不动点.

Section 后继不动点.
Variable F : 函数类型.
Variable F嵌入 : 为序数嵌入 F.
Variable α : 集合.
Variable Hα : α ⋵ 𝐎𝐍.

Definition 后继不动点 := 任意不动点 F α⁺.
Local Notation β := 后继不动点.
Local Notation Rec := 序数递归.

Lemma 后继不动点为之 : β ⋵ 𝐎𝐍 ∧ F β = β ∧ α ∈ β ∧
  ∀γ ⋵ 𝐎𝐍, F γ = γ → α ∈ γ → β ⋸ γ.
Proof with auto.
  assert (Hβ: β ⋵ 𝐎𝐍). apply β为序数...
  split3... apply β为不动点... split. apply 小于即后继小于等于... apply β任意大...
  intros γ Hγ 不动点γ Hαγ. 反证. apply 序数可换 in 反设...
  apply 集族并除去 in 反设 as [n [Hn H]].
  generalize dependent H. 归纳 n; intros H.
  - rewrite 序数递归_0 in H. apply 序数不稠密 with γ α...
  - apply 归纳假设. apply 序数嵌入双向保序 with F...
    apply 序数运算的递归为序数运算... apply F嵌入.
    rewrite 不动点γ, <- 序数递归_后继...
Qed.

Theorem 存在后继不动点 : ∃β ⋵ 𝐎𝐍, F β = β ∧ α ∈ β ∧
  ∀γ ⋵ 𝐎𝐍, F γ = γ → α ∈ γ → β ⋸ γ.
Proof. exists β. apply 后继不动点为之. Qed.

End 后继不动点.

Section 不动点枚举.
Variable F : 函数类型.
Variable F嵌入 : 为序数嵌入 F.
Variable F非平凡 : ∀α ⋵ 𝐎𝐍, F α⁺ ≠ α⁺.

Local Notation α₀ := (最小不动点 F).
Local Notation S := (后继不动点 F).
Definition 不动点枚举 := 序数递归 α₀ S.
Local Notation G := 不动点枚举.

Lemma 最小不动点为序数 : α₀ ⋵ 𝐎𝐍.
Proof. apply 最小不动点为之. auto. Qed.

Lemma 后继不动点为序数运算 : 为序数运算 S.
Proof. intros. apply 后继不动点为之; auto. Qed.

Lemma 不动点枚举为序数运算 : 为序数运算 G.
Proof. apply 序数运算的递归为序数运算. apply 最小不动点为序数. apply 后继不动点为序数运算. Qed.

Lemma 不动点枚举_0 : G ∅ = α₀.
Proof. apply 序数递归_0. Qed.

Lemma 不动点枚举_后继 : ∀α ⋵ 𝐎𝐍, G α⁺ = S (G α).
Proof. apply 序数递归_后继. Qed.

Lemma 不动点枚举_极限 : 极限处连续 G.
Proof. apply 序数递归_极限. Qed.

Lemma 不动点枚举在后继处递增 : 后继处递增 G.
Proof with auto.
  intros. rewrite 不动点枚举_后继... apply 后继不动点为之... apply 不动点枚举为序数运算...
Qed.

Theorem 不动点枚举为序数嵌入 : 为序数嵌入 G.
Proof. split3. apply 不动点枚举为序数运算. apply 不动点枚举在后继处递增. apply 不动点枚举_极限. Qed.

Corollary 存在不动点的不动点 : ∀α ⋵ 𝐎𝐍, ∃β ⋵ 𝐎𝐍, G β = β ∧ α ⋸ β.
Proof. intros. apply 不动点定理; auto. apply 不动点枚举为序数嵌入. Qed.

Theorem 不动点枚举枚举之 : ∀α ⋵ 𝐎𝐍, F (G α) = G α.
Proof with auto.
  超限归纳. 超限讨论 α.
  - rewrite 不动点枚举_0. apply 最小不动点为之...
  - rewrite 不动点枚举_后继... apply 后继不动点为之... apply 不动点枚举为序数运算...
  - rewrite 不动点枚举_极限, 上确界的嵌入等于嵌入集的上确界...
    2: { apply 非空除去. exists (不动点枚举 ∅). apply 替代介入. exists ∅... }
    2: { intros x Hx. apply 替代除去 in Hx as [β [Hβ Hx]]. subst.
      apply 不动点枚举为序数运算. eauto. }
    f_equal. 外延 x Hx.
    + apply 替代除去 in Hx as [β [Hβ Hx]]. subst.
      apply 替代除去 in Hβ as [γ [Hγ Hβ]]. subst.
      apply 替代介入. exists γ...
    + apply 替代除去 in Hx as [β [Hβ Hx]]. subst.
      apply 替代介入. exists (不动点枚举 β). split... symmetry...
Qed.

Theorem 不动点不为零 : ∀α ⋵ 𝐎𝐍, F ∅ ≠ ∅ → G α ≠ ∅.
Proof.
  intros α Hα HF0. pose proof (不动点枚举枚举之 α Hα).
  intros H0. rewrite H0 in H. auto.
Qed.

Lemma 最小不动点为极限 : G ∅ ⋵ 𝐋𝐈𝐌.
Proof with auto.
  rewrite 不动点枚举_0.
  destruct (序数要么为后继要么为极限 α₀ 最小不动点为序数)...
  exfalso. destruct H as [α [Hα H]]. apply F非平凡 with α...
  rewrite <- H. apply 最小不动点为之...
Qed.

Lemma 后继不动点为极限 : ∀α ⋵ 𝐎𝐍, G α⁺ ⋵ 𝐋𝐈𝐌.
Proof with auto.
  intros. destruct (序数要么为后继要么为极限 (不动点枚举 α⁺))... apply 不动点枚举为序数运算...
  exfalso. destruct H0 as [β [Hβ Heq]].
  apply F非平凡 with β... rewrite <- Heq. apply 不动点枚举枚举之...
Qed.

Theorem 不动点为极限 : ∀α ⋵ 𝐎𝐍, G α ⋵ 𝐋𝐈𝐌.
Proof with auto.
  intros α Hα. 超限讨论 α. apply 最小不动点为极限. apply 后继不动点为极限...
  apply 序数嵌入在极限处的值为极限... apply 不动点枚举为序数嵌入.
Qed.

Local Notation E := 不动点枚举.
Local Notation A := 任意不动点.

End 不动点枚举.
