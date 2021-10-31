(** Coq coding by choukh, Oct 2021 **)

Require Import BBST.Theory.Ordinal.

(* 练习2-3-1 *)
Fact 直积的替代定义 : ∀ A B, A × B = ⋃{{<a, b> | b ∊ B} | a ∊ A}. Admitted.
