(** Coq coding by choukh, Oct 2021 **)

Require Import Coq.Logic.ClassicalDescription.
Require Import BBST.Axiom.Meta.
Require Import BBST.Definition.Omega.

Fixpoint 嵌入 (n : nat) :=
  match n with
  | O => ∅
  | S m => (嵌入 m)⁺
  end.

Lemma 嵌入到ω : ∀ n : nat, 嵌入 n ∈ ω.
Proof. induction n; simpl. auto. apply ω归纳. apply IHn. Qed.
Global Hint Immediate 嵌入到ω : core.

Lemma 嵌入是单射 : ∀ n m : nat, 嵌入 n = 嵌入 m → n = m.
Proof.
  induction n; destruct m; simpl; intros H.
  - (* n = 0, m = 0 *) reflexivity.
  - (* n = 0, m = S m *) exfalso. apply 后继非空 with (嵌入 m). auto.
  - (* n = S n, m = 0 *) exfalso. apply 后继非空 with (嵌入 n). auto.
  - (* n = S n, m = S m *) apply 后继是单射 in H; auto.
Qed.

Lemma 投影存在 : ∀n ∈ ω, ∃ m : nat, 嵌入 m = n.
Proof.
  intros n Hn. 归纳 n.
  - exists 0. reflexivity.
  - destruct 归纳假设 as [k H]. subst. exists (S k). reflexivity.
Qed.

Lemma 投影唯一 : ∀n ∈ ω, uniqueness (λ m, 嵌入 m = n).
Proof. intros n Hn p q Hp Hq. subst. apply 嵌入是单射. auto. Qed.

Definition 投影 := λ n, iota 0 (λ m, 嵌入 m = n).

Theorem 先投影再嵌入 : ∀n ∈ ω, 嵌入 (投影 n) = n.
Proof.
  intros n Hn. unfold 投影. apply iota_spec.
  rewrite <- unique_existence. split.
  apply 投影存在; auto. apply 投影唯一; auto.
Qed.

Theorem 先嵌入再投影 : ∀ n : nat, 投影 (嵌入 n) = n.
Proof. intros n. apply 嵌入是单射. rewrite 先投影再嵌入; auto. Qed.

Corollary 投影是单射 : ∀ n m ∈ ω, 投影 n = 投影 m → n = m.
Proof.
  intros n Hn m Hm H.
  assert (嵌入 (投影 n) = 嵌入 (投影 m)). auto.
  do 2 rewrite 先投影再嵌入 in H0; auto.
Qed.

Lemma 先嵌入再后继再投影 : ∀ n : nat, S n = 投影 (嵌入 n)⁺.
Proof. intros. rewrite <- (先嵌入再投影 (S n)). reflexivity. Qed.

Lemma 先投影再后继再嵌入 : ∀n ∈ ω, n⁺ = 嵌入 (S (投影 n)).
Proof.
  intros n Hn. rewrite 先嵌入再后继再投影.
  do 2 rewrite 先投影再嵌入; auto.
Qed.
