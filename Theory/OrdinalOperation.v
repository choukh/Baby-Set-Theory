(** Coq coding by choukh, Oct 2021 **)

Require Import BBST.Theory.Ordinal.
Local Hint Resolve ğğä¸ºä¼ éç±» : core.
Local Hint Immediate Ïä¸ºåºæ°é : core.

Notation æééå¢ F := (ân â Ï, F n â F nâº).
Notation æéä¿åº F := (ân â Ï, âm â n, F m â F n).

Notation æéå¼±éå¢ F := (ân â Ï, F n â¸ F nâº).
Notation æéå¼±ä¿åº F := (ân â Ï, âm â n, F m â¸ F n).

Notation ä¸ºåºæ°è¿ç® F := (âÎ± âµ ğğ, F Î± âµ ğğ).
Notation åç»§å¤éå¢ F := (âÎ± âµ ğğ, F Î± â F Î±âº).
Notation æéå¤è¿ç»­ F := (âÎ± âµ ğğğ, Î± â  â â F Î± = sup{F Î² | Î² â Î±}).
Definition ä¸ºåºæ°åµå¥ := Î» F, ä¸ºåºæ°è¿ç® F â§ åç»§å¤éå¢ F â§ æéå¤è¿ç»­ F.

Definition ä¿åº := Î» F, âÎ± âµ ğğ, âÎ² â Î±, F Î² â F Î±.
Definition ååä¿åº := Î» F, â Î± Î² âµ ğğ, Î± â Î² â F Î± â F Î².
Definition éæ ç©·éé¾ := Î» F, âÎ± âµ ğğ, Î± â¸ F Î±.

Lemma å¼±éå¢æ ç©·åºåæéä¸èµ·å§æ å³ : ân â Ï, â F, ä¸ºåºæ°è¿ç® F â æéå¼±éå¢ F â
  sup {F k | k â Ï - nâº} = sup {F kâº | k â Ï - n}.
Proof with auto.
  intros n Hn F è¿ç® éå¢. å¤å»¶.
  - apply éæå¹¶é¤å» in H as [k [Hk H]]. apply åç¦»é¤å» in Hk as [Hk Hk'].
    apply éæå¹¶ä»å¥ with k. apply åç¦»ä»å¥... apply åºæ°ä¼ é_å³å¼± with (F k)...
  - apply éæå¹¶é¤å» in H as [k [Hk H]]. apply åç¦»é¤å» in Hk as [Hk Hk'].
    apply éæå¹¶ä»å¥ with kâºâº. apply åç¦»ä»å¥... 2: apply åºæ°ä¼ é_å³å¼± with (F kâº)...
    intros H'. apply Hk'. apply åç»§ä¿åº... apply åºæ°ä¼ é with kâºâº...
Qed.

Lemma å¼±ä¿åºæ ç©·åºåæéä¸èµ·å§æ å³ : ân â Ï, â F, ä¸ºåºæ°è¿ç® F â æéå¼±ä¿åº F â
  sup {F k | k â Ï} = sup {F k | k â Ï - n}.
Proof with auto.
  intros n Hn F è¿ç® ä¿åº. å¤å»¶.
  - apply éæå¹¶é¤å» in H as [k [Hk H]]. æä¸­ (k â n).
    + apply éæå¹¶ä»å¥ with n. apply åç¦»ä»å¥...
      apply åºæ°ä¼ é_å³å¼± with (F k)...
    + apply éæå¹¶ä»å¥ with k... apply åç¦»ä»å¥...
  - apply éæå¹¶é¤å» in H as [k [Hk H]].
    apply åç¦»ä¹ç¶é in Hk. apply éæå¹¶ä»å¥ with k...
Qed.

Theorem åºæ°åµå¥ä¿åº : â F, ä¸ºåºæ°åµå¥ F â ä¿åº F.
Proof with auto.
  intros F [è¿ç® [éå¢ è¿ç»­]]. unfold ä¿åº.
  è¶éå½çº³. intros Î² å°äº. è¶éè®¨è®º Î±.
  - ç©ºéå½è°¬.
  - apply åç»§é¤å» in å°äº as []. apply åºæ°ä¼ é with (F Î±)... subst...
  - rewrite (è¿ç»­ Î±)... apply éæå¹¶ä»å¥ with Î²âº.
    apply æéåºæ°æå¶ä»»æåç´ çåç»§... apply éå¢. eauto.
Qed.

Theorem ä¿åºè¿ç®ååä¿åº : â F, ä¸ºåºæ°è¿ç® F â ä¿åº F â ååä¿åº F.
Proof with auto.
  intros F HF ä¿åº Î± HÎ± Î² HÎ². split...
  intros Hlt. destruct (åºæ°ä¸æ­§ Î± HÎ± Î² HÎ²) as [|[]]...
  - exfalso. subst. apply åºæ°åèªå with (F Î²)...
  - exfalso. apply ä¿åº in H... apply åºæ°å¯æ¢ in H...
Qed.

Corollary åºæ°åµå¥ååä¿åº : â F, ä¸ºåºæ°åµå¥ F â ååä¿åº F.
Proof. intros. apply ä¿åºè¿ç®ååä¿åº. apply H. apply åºæ°åµå¥ä¿åº, H. Qed.

Theorem ä¿åºè¿ç®éæ ç©·éé¾ : â F, ä¸ºåºæ°è¿ç® F â ä¿åº F â éæ ç©·éé¾ F.
Proof with auto.
  intros F è¿ç® ä¿åº Î± HÎ±. åè¯. apply åºæ°å¯æ¢ in åè®¾...
  generalize dependent Î±. è¶éå½çº³. intros Hlt. apply å½çº³åè®¾ with (F Î±)...
Qed.

Corollary åºæ°åµå¥éæ ç©·éé¾ : â F, ä¸ºåºæ°åµå¥ F â éæ ç©·éé¾ F.
Proof. intros. apply ä¿åºè¿ç®éæ ç©·éé¾. apply H. apply åºæ°åµå¥ä¿åº, H. Qed.

Theorem ä¿åºè¿ç®ä¸ºç±»åå° : â F, ä¸ºåºæ°è¿ç® F â ä¿åº F â ä¸ºç±»åå° ğğ F.
Proof with auto.
  intros F è¿ç® ä¿åº Î± HÎ± Î² HÎ² ç¸ç­.
  destruct (åºæ°ä¸æ­§ Î± HÎ± Î² HÎ²) as [|[]]; auto; exfalso; apply ä¿åº in H...
  apply å°äºåä¸ç­ with (F Î²) (F Î±)...
  apply å°äºåä¸ç­ with (F Î±) (F Î²)...
Qed.

Corollary åºæ°åµå¥ä¸ºç±»åå° : â F, ä¸ºåºæ°åµå¥ F â ä¸ºç±»åå° ğğ F.
Proof. intros. apply ä¿åºè¿ç®ä¸ºç±»åå°. apply H. apply åºæ°åµå¥ä¿åº, H. Qed.

Theorem åºæ°åµå¥å¨æéå¤çå¼ä¸ºæé : â F, ä¸ºåºæ°åµå¥ F â âÎ± âµ ğğğ, Î± â  â â F Î± âµ ğğğ.
Proof with auto.
  intros F [è¿ç® [éå¢ è¿ç»­]] Î± æé H0. copy æé as [HÎ± _].
  rewrite è¿ç»­... split.
  - apply åºæ°éçå¹¶ä¸ºåºæ°. intros y Hy.
    apply æ¿ä»£é¤å» in Hy as [Î¾ [HÎ¾ HFÎ¾]]. subst y. apply è¿ç®. eauto.
  - å¤å»¶ Î² HÎ².
    + apply å¹¶éé¤å» in HÎ² as [Î³ [HÎ³ HÎ²]].
      apply éæå¹¶é¤å» in HÎ³ as [Î¾ [HÎ¾ HFÎ¾]].
      apply éæå¹¶ä»å¥ with Î¾... apply åºæ°ä¼ é with Î³... apply è¿ç®. eauto.
    + apply éæå¹¶é¤å» in HÎ² as [Î¾ [HÎ¾ HFÎ¾]]. apply å¹¶éä»å¥ with (F Î¾)...
      apply éæå¹¶ä»å¥ with Î¾âº... apply æéåºæ°æå¶ä»»æåç´ çåç»§... apply éå¢... eauto.
Qed.

Theorem ä¸ç¡®ççåµå¥ç­äºåµå¥éçä¸ç¡®ç : â F, ä¸ºåºæ°åµå¥ F â
  â A, A â  â â A âª½ ğğ â F (sup A) = sup {F Î± | Î± â A}.
Proof with auto.
  intros F HF A H0 HA.
  assert (Hs: sup A âµ ğğ). apply åºæ°éçå¹¶ä¸ºåºæ°...
  assert (HFs: F (sup A) âµ ğğ). apply HF...
  assert (Hr: {F Î± | Î± â A} âª½ ğğ). {
    intros x Hx. apply æ¿ä»£é¤å» in Hx as [Î± [HÎ± H]]. subst x. apply HF...
  }
  assert (Hsr: sup {F Î± | Î± â A} âµ ğğ). apply åºæ°éçå¹¶ä¸ºåºæ°...
  apply åå«çåå¯¹ç§°æ§.
  - remember (sup A) as Ï. è¶éè®¨è®º Ï.
    + apply å°äºç­äºå³åå«... apply åºæ°éçå¹¶ä¸ºä¸ç... apply æ¿ä»£ä»å¥_èªå¨... rewrite H1. 
      apply ä»é¶æä¸ä¹å¹¶ä¸ºé¶ in H1 as []. exfalso... subst...
    + apply å°äºç­äºå³åå«... apply åºæ°éçå¹¶ä¸ºä¸ç... apply æ¿ä»£ä»å¥_èªå¨.
      apply ä¸ºåç»§çä¸ç¡®çå¨åºæ°éå... exists Ï...
    + intros x Hx. copy HF as [_ [_ è¿ç»­]]. rewrite è¿ç»­ in Hx...
      apply éæå¹¶é¤å» in Hx as [Î± [HÎ± Hx]]. rewrite HeqÏ in HÎ±.
      apply å¹¶éé¤å» in HÎ± as [Î² [HÎ² HÎ±]]. apply éæå¹¶ä»å¥ with Î²...
      apply åºæ°ä¼ é with (F Î±)... apply åºæ°åµå¥ä¿åº...
  - intros x Hx. apply éæå¹¶é¤å» in Hx as [Î± [HÎ± Hx]].
    apply åºæ°éçå¹¶ä¸ºä¸ç in HA as [_ Hle]. apply Hle in HÎ± as [].
    apply åºæ°ä¼ é with (F Î±)... apply åºæ°åµå¥ä¿åº... congruence.
Qed.

Section åºæ°éå½.
Import è¶ééå½æ¨¡æ¿_ä¸æå®.
Variable yâ : éå.
Variable F : å½æ°ç±»å.

Definition åºæ°éå½ := ä¸æå® yâ F (Î» f, sup (ran f)).
Local Notation ğ¥ := åºæ°éå½.

Theorem åºæ°éå½_0 : ğ¥ â = yâ.
Proof. apply ä¸æå®_0. Qed.

Theorem åºæ°éå½_åç»§ : âÎ± âµ ğğ, ğ¥ Î±âº = F (ğ¥ Î±).
Proof. apply ä¸æå®_åç»§. Qed.

Theorem åºæ°éå½_æé : æéå¤è¿ç»­ ğ¥.
Proof. intros Î± æé éé¶. rewrite <- ç±»å½æ°éå¶ä¹å¼å. apply ä¸æå®_æé; auto. Qed.

End åºæ°éå½.

Theorem åºæ°è¿ç®çéå½ä¸ºåºæ°è¿ç® : âyâ âµ ğğ, â F, ä¸ºåºæ°è¿ç® F â ä¸ºåºæ°è¿ç® (åºæ°éå½ yâ F).
Proof with auto.
  intros yâ Hyâ F H. è¶éå½çº³. è¶éè®¨è®º Î±.
  - rewrite åºæ°éå½_0...
  - rewrite åºæ°éå½_åç»§...
  - rewrite åºæ°éå½_æé...
    apply åºæ°éçå¹¶ä¸ºåºæ°. intros x Hx.
    apply æ¿ä»£é¤å» in Hx as [Î² [HÎ² Hx]]. subst. apply å½çº³åè®¾...
Qed.

Section ç¼ºé¶éå½.
Import è¶ééå½æ¨¡æ¿_ä¸æå®.
Variable yâ : éå.
Variable F : å½æ°ç±»å.

Definition ç¼ºé¶éå½ := ä¸æå® yâ F (Î» f, sup (ran (f â¾ (dom f - {â,})))).
Local Notation ğ¥ := ç¼ºé¶éå½.

Theorem ç¼ºé¶éå½_0 : ğ¥ â = yâ.
Proof. apply ä¸æå®_0. Qed.

Theorem ç¼ºé¶éå½_åç»§ : âÎ± âµ ğğ, ğ¥ Î±âº = F (ğ¥ Î±).
Proof. apply ä¸æå®_åç»§. Qed.

Theorem ç¼ºé¶éå½_æé : âÎ± âµ ğğğ, Î± â  â â ğ¥ Î± = sup{ğ¥ Î² | Î² â Î± - {â,}}.
Proof with auto.
  intros Î± æé éé¶. rewrite <- ç±»å½æ°éå¶ä¹å¼å. set (ğ¥ â Î±) as f.
  replace (ğ¥ â Î± - {â,}) with (f â¾ (dom f - {â,})). apply ä¸æå®_æé...
  unfold f. rewrite ç±»å½æ°éå¶ä¹å®ä¹å. apply ç±»å½æ°éå¶å°ç¶åå­...
Qed.

End ç¼ºé¶éå½.

Theorem åºæ°è¿ç®çç¼ºé¶éå½ä¸ºåºæ°è¿ç® : âyâ âµ ğğ, â F, ä¸ºåºæ°è¿ç® F â ä¸ºåºæ°è¿ç® (ç¼ºé¶éå½ yâ F).
Proof with auto.
  intros yâ Hyâ F H. è¶éå½çº³. è¶éè®¨è®º Î±.
  - rewrite ç¼ºé¶éå½_0...
  - rewrite ç¼ºé¶éå½_åç»§...
  - rewrite ç¼ºé¶éå½_æé...
    apply åºæ°éçå¹¶ä¸ºåºæ°. intros x Hx. apply æ¿ä»£é¤å» in Hx as [Î² [HÎ² Hx]].
    apply åç¦»ä¹ç¶é in HÎ². subst. apply å½çº³åè®¾...
Qed.

Section ä»»æä¸å¨ç¹.
Variable F : å½æ°ç±»å.
Variable Fåµå¥ : ä¸ºåºæ°åµå¥ F.
Variable Î± : éå.
Variable HÎ± : Î± âµ ğğ.

Local Notation G := (åºæ°éå½ Î± F).
Local Notation A := {G n | n â Ï}.
Definition ä»»æä¸å¨ç¹ := sup A.
Local Notation Î² := ä»»æä¸å¨ç¹.

Local Lemma Aéç©º : A â  â.
Proof. apply éç©ºé¤å». exists (G â). apply æ¿ä»£ä»å¥_èªå¨; auto. Qed.

Local Lemma Aä¸ºåºæ°é : A âª½ ğğ.
Proof with auto.
  intros x Hx. apply æ¿ä»£é¤å» in Hx as [n [Hn HGn]]. subst x.
  apply åºæ°è¿ç®çéå½ä¸ºåºæ°è¿ç®... apply Fåµå¥.
Qed.

Local Lemma Î²ä¸ºåºæ° : Î² âµ ğğ.
Proof. apply åºæ°éçå¹¶ä¸ºåºæ°. apply Aä¸ºåºæ°é. Qed.

Local Lemma Î²ä»»æå¤§ : Î± â¸ Î².
Proof with auto.
  apply åºæ°éçå¹¶ä¸ºä¸ç. apply Aä¸ºåºæ°é.
  apply æ¿ä»£ä»å¥. exists â. split... rewrite åºæ°éå½_0...
Qed.

Local Lemma Î²ä¸ºä¸å¨ç¹ : F Î² = Î².
Proof with auto.
  unfold Î². rewrite (ä¸ç¡®ççåµå¥ç­äºåµå¥éçä¸ç¡®ç F Fåµå¥ A Aéç©º Aä¸ºåºæ°é). å¤å»¶.
  - apply éæå¹¶é¤å» in H as [Î³ [HÎ³ H]].
    apply æ¿ä»£é¤å» in HÎ³ as [n [Hn HÎ³]]. subst.
    apply å¹¶éä»å¥ with (G nâº). apply æ¿ä»£ä»å¥_èªå¨... rewrite åºæ°éå½_åç»§...
  - apply å¹¶éé¤å» in H as [Î³ [HÎ³ Hx]].
    apply æ¿ä»£é¤å» in HÎ³ as [n [Hn HÎ³]]. subst.
    apply éæå¹¶ä»å¥ with (G n). apply æ¿ä»£ä»å¥_èªå¨... copy Fåµå¥ as [HF _].
    assert (G n âµ ğğ). apply åºæ°è¿ç®çéå½ä¸ºåºæ°è¿ç®...
    generalize dependent x. apply å°äºç­äºå³åå«...
    apply ä¿åºè¿ç®éæ ç©·éé¾... apply åºæ°åµå¥ä¿åº...
Qed.

Lemma ä¸å¨ç¹ä¸ºä¹ : Î² âµ ğğ â§ F Î² = Î² â§ Î± â¸ Î².
Proof. split3. apply Î²ä¸ºåºæ°. apply Î²ä¸ºä¸å¨ç¹. apply Î²ä»»æå¤§. Qed.

(* Veblenä¸å¨ç¹å®çï¼åºæ°åµå¥å­å¨ä»»æå¤§çä¸å¨ç¹ *)
Theorem ä¸å¨ç¹å®ç : âÎ² âµ ğğ, F Î² = Î² â§ Î± â¸ Î².
Proof. exists Î². apply ä¸å¨ç¹ä¸ºä¹. Qed.

End ä»»æä¸å¨ç¹.

Section æå°ä¸å¨ç¹.
Variable F : å½æ°ç±»å.
Variable Fåµå¥ : ä¸ºåºæ°åµå¥ F.

Local Notation Î² := (ä»»æä¸å¨ç¹ F â).

Definition æå°ä¸å¨ç¹ := inf {Î³ â Î²âº | F Î³ = Î³}.
Local Notation Î²â := æå°ä¸å¨ç¹.

Lemma æå°ä¸å¨ç¹ä¸ºä¹ : Î²â âµ ğğ â§ F Î²â = Î²â â§ âÎ³ âµ ğğ, F Î³ = Î³ â Î²â â¸ Î³.
Proof. apply æ»¡è¶³æ¡ä»¶çæå°åºæ°ä¸ºä¹. apply Î²ä¸ºåºæ°; auto. apply Î²ä¸ºä¸å¨ç¹; auto. Qed.

Theorem å­å¨æå°ä¸å¨ç¹ : âÎ² âµ ğğ, F Î² = Î² â§ âÎ³ âµ ğğ, F Î³ = Î³ â Î² â¸ Î³.
Proof. exists Î²â. apply æå°ä¸å¨ç¹ä¸ºä¹. Qed.

End æå°ä¸å¨ç¹.

Section åç»§ä¸å¨ç¹.
Variable F : å½æ°ç±»å.
Variable Fåµå¥ : ä¸ºåºæ°åµå¥ F.
Variable Î± : éå.
Variable HÎ± : Î± âµ ğğ.

Definition åç»§ä¸å¨ç¹ := ä»»æä¸å¨ç¹ F Î±âº.
Local Notation Î² := åç»§ä¸å¨ç¹.
Local Notation ğ¥ := åºæ°éå½.

Lemma åç»§ä¸å¨ç¹ä¸ºä¹ : Î² âµ ğğ â§ F Î² = Î² â§ Î± â Î² â§
  âÎ³ âµ ğğ, F Î³ = Î³ â Î± â Î³ â Î² â¸ Î³.
Proof with auto.
  assert (HÎ²: Î² âµ ğğ). apply Î²ä¸ºåºæ°...
  split3... apply Î²ä¸ºä¸å¨ç¹... split. apply å°äºå³åç»§å°äºç­äº... apply Î²ä»»æå¤§...
  intros Î³ HÎ³ ä¸å¨ç¹Î³ HÎ±Î³. åè¯. apply åºæ°å¯æ¢ in åè®¾...
  apply éæå¹¶é¤å» in åè®¾ as [n [Hn H]].
  generalize dependent H. å½çº³ n; intros H.
  - rewrite åºæ°éå½_0 in H. apply åºæ°ä¸ç¨ å¯ with Î³ Î±...
  - apply å½çº³åè®¾. apply åºæ°åµå¥ååä¿åº with F...
    apply åºæ°è¿ç®çéå½ä¸ºåºæ°è¿ç®... apply Fåµå¥.
    rewrite ä¸å¨ç¹Î³, <- åºæ°éå½_åç»§...
Qed.

Theorem å­å¨åç»§ä¸å¨ç¹ : âÎ² âµ ğğ, F Î² = Î² â§ Î± â Î² â§
  âÎ³ âµ ğğ, F Î³ = Î³ â Î± â Î³ â Î² â¸ Î³.
Proof. exists Î². apply åç»§ä¸å¨ç¹ä¸ºä¹. Qed.

End åç»§ä¸å¨ç¹.

Section ä¸å¨ç¹æä¸¾.
Variable F : å½æ°ç±»å.
Variable Fåµå¥ : ä¸ºåºæ°åµå¥ F.
Variable Féå¹³å¡ : âÎ± âµ ğğ, F Î±âº â  Î±âº.

Local Notation Î±â := (æå°ä¸å¨ç¹ F).
Local Notation S := (åç»§ä¸å¨ç¹ F).
Definition ä¸å¨ç¹æä¸¾ := åºæ°éå½ Î±â S.
Local Notation G := ä¸å¨ç¹æä¸¾.

Lemma æå°ä¸å¨ç¹ä¸ºåºæ° : Î±â âµ ğğ.
Proof. apply æå°ä¸å¨ç¹ä¸ºä¹. auto. Qed.

Lemma åç»§ä¸å¨ç¹ä¸ºåºæ°è¿ç® : ä¸ºåºæ°è¿ç® S.
Proof. intros. apply åç»§ä¸å¨ç¹ä¸ºä¹; auto. Qed.

Lemma ä¸å¨ç¹æä¸¾ä¸ºåºæ°è¿ç® : ä¸ºåºæ°è¿ç® G.
Proof. apply åºæ°è¿ç®çéå½ä¸ºåºæ°è¿ç®. apply æå°ä¸å¨ç¹ä¸ºåºæ°. apply åç»§ä¸å¨ç¹ä¸ºåºæ°è¿ç®. Qed.

Lemma ä¸å¨ç¹æä¸¾_0 : G â = Î±â.
Proof. apply åºæ°éå½_0. Qed.

Lemma ä¸å¨ç¹æä¸¾_åç»§ : âÎ± âµ ğğ, G Î±âº = S (G Î±).
Proof. apply åºæ°éå½_åç»§. Qed.

Lemma ä¸å¨ç¹æä¸¾_æé : æéå¤è¿ç»­ G.
Proof. apply åºæ°éå½_æé. Qed.

Lemma ä¸å¨ç¹æä¸¾å¨åç»§å¤éå¢ : åç»§å¤éå¢ G.
Proof with auto.
  intros. rewrite ä¸å¨ç¹æä¸¾_åç»§... apply åç»§ä¸å¨ç¹ä¸ºä¹... apply ä¸å¨ç¹æä¸¾ä¸ºåºæ°è¿ç®...
Qed.

Theorem ä¸å¨ç¹æä¸¾ä¸ºåºæ°åµå¥ : ä¸ºåºæ°åµå¥ G.
Proof. split3. apply ä¸å¨ç¹æä¸¾ä¸ºåºæ°è¿ç®. apply ä¸å¨ç¹æä¸¾å¨åç»§å¤éå¢. apply ä¸å¨ç¹æä¸¾_æé. Qed.

Corollary å­å¨ä¸å¨ç¹çä¸å¨ç¹ : âÎ± âµ ğğ, âÎ² âµ ğğ, G Î² = Î² â§ Î± â¸ Î².
Proof. intros. apply ä¸å¨ç¹å®ç; auto. apply ä¸å¨ç¹æä¸¾ä¸ºåºæ°åµå¥. Qed.

Theorem ä¸å¨ç¹æä¸¾æä¸¾ä¹ : âÎ± âµ ğğ, F (G Î±) = G Î±.
Proof with auto.
  è¶éå½çº³. è¶éè®¨è®º Î±.
  - rewrite ä¸å¨ç¹æä¸¾_0. apply æå°ä¸å¨ç¹ä¸ºä¹...
  - rewrite ä¸å¨ç¹æä¸¾_åç»§... apply åç»§ä¸å¨ç¹ä¸ºä¹... apply ä¸å¨ç¹æä¸¾ä¸ºåºæ°è¿ç®...
  - rewrite ä¸å¨ç¹æä¸¾_æé, ä¸ç¡®ççåµå¥ç­äºåµå¥éçä¸ç¡®ç...
    2: { apply éç©ºé¤å». exists (ä¸å¨ç¹æä¸¾ â). apply æ¿ä»£ä»å¥. exists â... }
    2: { intros x Hx. apply æ¿ä»£é¤å» in Hx as [Î² [HÎ² Hx]]. subst.
      apply ä¸å¨ç¹æä¸¾ä¸ºåºæ°è¿ç®. eauto. }
    f_equal. å¤å»¶ x Hx.
    + apply æ¿ä»£é¤å» in Hx as [Î² [HÎ² Hx]]. subst.
      apply æ¿ä»£é¤å» in HÎ² as [Î³ [HÎ³ HÎ²]]. subst.
      apply æ¿ä»£ä»å¥. exists Î³...
    + apply æ¿ä»£é¤å» in Hx as [Î² [HÎ² Hx]]. subst.
      apply æ¿ä»£ä»å¥. exists (ä¸å¨ç¹æä¸¾ Î²). split... symmetry...
Qed.

Theorem ä¸å¨ç¹ä¸ä¸ºé¶ : âÎ± âµ ğğ, F â â  â â G Î± â  â.
Proof.
  intros Î± HÎ± HF0. pose proof (ä¸å¨ç¹æä¸¾æä¸¾ä¹ Î± HÎ±).
  intros H0. rewrite H0 in H. auto.
Qed.

Lemma æå°ä¸å¨ç¹ä¸ºæé : G â âµ ğğğ.
Proof with auto.
  rewrite ä¸å¨ç¹æä¸¾_0.
  destruct (åºæ°è¦ä¹ä¸ºåç»§è¦ä¹ä¸ºæé Î±â æå°ä¸å¨ç¹ä¸ºåºæ°)...
  exfalso. destruct H as [Î± [HÎ± H]]. apply Féå¹³å¡ with Î±...
  rewrite <- H. apply æå°ä¸å¨ç¹ä¸ºä¹...
Qed.

Lemma åç»§ä¸å¨ç¹ä¸ºæé : âÎ± âµ ğğ, G Î±âº âµ ğğğ.
Proof with auto.
  intros. destruct (åºæ°è¦ä¹ä¸ºåç»§è¦ä¹ä¸ºæé (ä¸å¨ç¹æä¸¾ Î±âº))... apply ä¸å¨ç¹æä¸¾ä¸ºåºæ°è¿ç®...
  exfalso. destruct H0 as [Î² [HÎ² Heq]].
  apply Féå¹³å¡ with Î²... rewrite <- Heq. apply ä¸å¨ç¹æä¸¾æä¸¾ä¹...
Qed.

Theorem ä¸å¨ç¹ä¸ºæé : âÎ± âµ ğğ, G Î± âµ ğğğ.
Proof with auto.
  intros Î± HÎ±. è¶éè®¨è®º Î±. apply æå°ä¸å¨ç¹ä¸ºæé. apply åç»§ä¸å¨ç¹ä¸ºæé...
  apply åºæ°åµå¥å¨æéå¤çå¼ä¸ºæé... apply ä¸å¨ç¹æä¸¾ä¸ºåºæ°åµå¥.
Qed.

Local Notation E := ä¸å¨ç¹æä¸¾.
Local Notation A := ä»»æä¸å¨ç¹.

End ä¸å¨ç¹æä¸¾.

Definition å¯¹ä¸ç¡®çå°é­ := Î» C, â A, A â  â â A âª½ C â sup A âµ C.
Definition æç := Î» C, âÎ± âµ ğğ, âÎ² âµ C, Î² â¸ Î±.
Definition æ ç := Î» C, âÎ± âµ ğğ, âÎ² âµ C, Î± â Î².

Theorem ğğæ çå­ç±»ä¸ºçç±» : â C, C â« ğğ â æ ç C â ä¸ºçç±» C.
Proof.
  intros C å­ç±» æ ç [A ä¸ºéå]. apply ğğä¸ºçç±».
  exists (sup A). intros Î± HÎ±. apply æ ç in HÎ± as [Î² [HÎ² HÎ±]].
  apply å¹¶éä»å¥ with Î²; auto.
Qed.

Section æ çå­ç±»æä¸¾.
Variable C : ç±».
Variable Cä¸ºå­ç±» : C â« ğğ.
Variable Cæ ç : æ ç C.

Local Definition Gå³ç³» := Î» f y, y âµ C â§ y â ran f â§ âx âµ C, x â ran f â y â¸ x.

Local Lemma Gå³ç³»æå½æ°æ§ : â f, â! y, Gå³ç³» f y.
Proof with auto.
  intros. rewrite <- unique_existence. split.
  - assert (âÎ± âµ C, Î± â ran f). {
      åè¯. apply ğğæ çå­ç±»ä¸ºçç±» with C... exists (ran f)...
      intros Î± HÎ±. åè¯. firstorder.
    }
    destruct H as [Î± HÎ±]. assert (HÎ±o: Î± âµ ğğ). destruct HÎ±...
    set (Î» Î², Î² âµ C â§ Î² â ran f) as P.
    pose proof (å­å¨æ»¡è¶³æ¡ä»¶çæå°åºæ° Î± HÎ±o P HÎ±) as [Î¼ [HÎ¼o [HÎ¼ Hle]]].
    destruct HÎ¼ as [HÎ¼ HÎ¼']. exists Î¼.
    split... split... intros x Hx Hx'. æä¸­ (x â¸ Î±).
    + apply Hle... split...
    + apply åºæ°å¯æ¢ in H... apply åºæ°ä¼ é_å¼± with Î±...
  - intros x y [HxC [Hx H1]] [HyC [Hy H2]].
    apply H1 in Hy... apply H2 in Hx...
    destruct Hx; destruct Hy... exfalso. apply åºæ°å¯æ¢ with x y...
Qed.
Local Hint Immediate Gå³ç³»æå½æ°æ§ : core.

Local Definition G := Î» f, æè¿° (Gå³ç³» f).

Local Lemma Gè§è : â f, dom f âµ ğğ â Gå³ç³» f (G f).
Proof. intros. unfold G. apply æè¿°å¬ç. apply Gå³ç³»æå½æ°æ§. Qed.

Definition æä¸¾ := è¶ééå½ G.

(* æä¸¾æ¯ğğå°å¶å­ç±»çæ å° *)
Lemma æä¸¾è§èç² : âÎ± âµ ğğ, æä¸¾ Î± âµ C.
Proof with auto.
  intros. unfold æä¸¾. rewrite è¶ééå½å®ç...
  apply Gè§è. rewrite ç±»å½æ°éå¶ä¹å®ä¹å...
Qed.

Corollary æä¸¾ä¸ºåºæ°è¿ç® : ä¸ºåºæ°è¿ç® æä¸¾.
Proof. intros. apply Cä¸ºå­ç±», æä¸¾è§èç²; auto. Qed.

(* æä¸¾å¼ä¸ä¹åä¸å *)
Lemma æä¸¾è§èä¹ : âÎ± âµ ğğ, âÎ² â Î±, æä¸¾ Î± â {æä¸¾ Î² | Î² â Î±}.
Proof with auto.
  intros Î± HÎ± Î² HÎ²Î±. intros H. unfold æä¸¾ in H.
  rewrite è¶ééå½å®ç in H... apply Gè§è with (è¶ééå½ G â Î±).
  rewrite ç±»å½æ°éå¶ä¹å®ä¹å... rewrite ç±»å½æ°éå¶ä¹å¼å...
Qed.

(* æä¸¾å¼æ¯ä¸ä¹åä¸åçæå°åºæ° *)
Lemma æä¸¾è§èä¸ : âÎ± âµ ğğ, âÎ¾ âµ C, Î¾ â {æä¸¾ Î² | Î² â Î±} â æä¸¾ Î± â¸ Î¾.
Proof with auto.
  intros Î± HÎ± Î¾ HÎ¾ H. unfold æä¸¾. rewrite è¶ééå½å®ç...
  apply Gè§è... rewrite ç±»å½æ°éå¶ä¹å®ä¹å... rewrite ç±»å½æ°éå¶ä¹å¼å...
Qed.

Theorem æä¸¾è¿ç®ä¿åº : ä¿åº æä¸¾.
Proof with auto.
  intros Î± HÎ± Î² HÎ²Î±. assert (HÎ²: Î² âµ ğğ). eauto.
  assert (æä¸¾ Î± â {æä¸¾ Î³ | Î³ â Î²}). {
    intros H. apply æ¿ä»£é¤å» in H as [Î³ [HÎ³ H]].
    apply æä¸¾è§èä¹ with Î± Î²... apply æ¿ä»£ä»å¥.
    exists Î³. split... apply åºæ°ä¼ é with Î²...
  }
  apply æä¸¾è§èä¸ in H as []... 2: apply æä¸¾è§èç²...
  exfalso. apply æä¸¾è§èä¹ with Î± Î²... apply æ¿ä»£ä»å¥. exists Î²...
Qed.

End æ çå­ç±»æä¸¾.
