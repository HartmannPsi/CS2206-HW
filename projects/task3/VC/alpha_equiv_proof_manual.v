Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import alpha_equiv_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
From SimpleC.EE Require Import ast_lib.
From SimpleC.EE Require Import malloc.
From SimpleC.EE Require Import super_poly_sll2.
Local Open Scope sac.

Lemma proof_of_alpha_equiv_entail_wit_1 : alpha_equiv_entail_wit_1.
Proof.
  pre_process.
  unfold termtypeID in *.
  destruct term1; lia.
Qed.

Lemma proof_of_alpha_equiv_return_wit_1_1 : alpha_equiv_return_wit_1_1.
Proof.
  pre_process.
  rewrite <- derivable1_orp_intros1.
  rewrite H3, H4.
  unfold store_term.
  Exists y z.
  entailer!.
  intros Hc.
  inversion Hc.
  pose proof list_Z_eq2eqb str1 str2 H13.
  unfold list_Z_cmp in H0.
  rewrite H14 in H0.
  congruence.
Qed.

Lemma proof_of_alpha_equiv_return_wit_1_2 : alpha_equiv_return_wit_1_2.
Proof.
  pre_process.
  rewrite <- derivable1_orp_intros2.
  rewrite H3, H4.
  unfold store_term.
  Exists y z.
  entailer!.
  apply AlphaVar.
  unfold list_Z_cmp in H0.
  rewrite H in H0.
  destruct (list_Z_eqb str1 str2) eqn:Heq; [ | congruence].
  apply (list_Z_eqb2eq str1 str2 Heq).
Qed.

Lemma proof_of_alpha_equiv_return_wit_2 : alpha_equiv_return_wit_2.
Proof.
  pre_process.
  rewrite <- derivable1_orp_intros1.
  rewrite H3, H2.
  unfold store_term.
  entailer!.
  intros Hc; inversion Hc.
  congruence.
Qed.  

Lemma proof_of_alpha_equiv_return_wit_3_1 : alpha_equiv_return_wit_3_1.
Proof.
  pre_process.
  rewrite <- derivable1_orp_intros1.
  rewrite H4, H5.
  unfold store_term.
  entailer!.
  intros Hc; inversion Hc.
  destruct H18; try congruence. 
Qed.

Lemma proof_of_alpha_equiv_return_wit_3_2 : alpha_equiv_return_wit_3_2.
Proof.
  pre_process.
  rewrite <- derivable1_orp_intros2.
  rewrite H4, H5.
  unfold store_term.
  entailer!.
  apply AlphaConst; [auto | right; auto].
Qed.

Lemma proof_of_alpha_equiv_return_wit_4 : alpha_equiv_return_wit_4.
Proof.
  pre_process.
  rewrite <- derivable1_orp_intros2.
  rewrite H4, H3.
  unfold store_term.
  entailer!.
  apply AlphaConst; [auto | left; auto].
Qed.

Lemma proof_of_alpha_equiv_return_wit_5_1 : alpha_equiv_return_wit_5_1.
Proof.
  pre_process.
  rewrite <- derivable1_orp_intros2.
  rewrite H8, H7.
  unfold store_term; fold store_term.
  Exists y1 z1 y2 z2.
  entailer!.
  apply AlphaApply; try auto.
Qed.

Lemma proof_of_alpha_equiv_return_wit_5_2 : alpha_equiv_return_wit_5_2.
Proof.
  pre_process.
Qed.

Lemma proof_of_alpha_equiv_return_wit_5_3 : alpha_equiv_return_wit_5_3.
Proof. 
  pre_process.
Qed.

Lemma proof_of_alpha_equiv_return_wit_5_4 : alpha_equiv_return_wit_5_4.
Proof.
  pre_process.
  rewrite <- derivable1_orp_intros1.
  rewrite H7, H8.
  unfold store_term; fold store_term.
  Exists y1 z1 y2 z2.
  entailer!.
  contradict H1.
  inversion H1.
  auto.
Qed.

Lemma proof_of_alpha_equiv_return_wit_5_5 : alpha_equiv_return_wit_5_5.
Proof.
  pre_process.
Qed.

Lemma proof_of_alpha_equiv_return_wit_5_6 : alpha_equiv_return_wit_5_6.
Proof.
  pre_process.
  rewrite <- derivable1_orp_intros1.
  rewrite H4, H5.
  unfold store_term; fold store_term.
  Exists y1 z1 y2 z2.
  entailer!.
  contradict H1.
  inversion H1.
  auto.
Qed.

Lemma proof_of_alpha_equiv_return_wit_6 : alpha_equiv_return_wit_6.
Proof.
  pre_process.
  rewrite <- derivable1_orp_intros1.
  rewrite H2, H3.
  unfold store_term; fold store_term.
  Exists y1 z1 y2 z2.
  entailer!.
  contradict H.
  inversion H.
  auto.
Qed.

Lemma proof_of_alpha_equiv_return_wit_7_1 : alpha_equiv_return_wit_7_1.
Proof.
  pre_process.
  rewrite <- derivable1_orp_intros2.
  rewrite H6, H7.
  unfold store_term; fold store_term.
  Exists y1 z1 y2 z2.
  entailer!.
  apply AlphaQuant; [auto | left; split; [ | auto]].
  unfold list_Z_cmp in H2.
  destruct (list_Z_eqb qv1 qv2) eqn:Heq; [reflexivity | congruence].
Qed.

Lemma proof_of_alpha_equiv_return_wit_7_2 : alpha_equiv_return_wit_7_2.
Proof.
  pre_process.
  rewrite <- derivable1_orp_intros1.
  rewrite H6, H7.
  unfold store_term; fold store_term.
  Exists y1 z1 y2 z2.
  entailer!.
  contradict H0.
  inversion H0.
  destruct H24 as [[Ha Hb] | Hc].
  + auto.
  + destruct Hc as [x Hx].
  Admitted. 

Lemma proof_of_alpha_equiv_return_wit_8_1 : alpha_equiv_return_wit_8_1.
Proof. 
    pre_process.
    rewrite H, H7, H8.
    rewrite <- derivable1_orp_intros2.
    unfold store_term; fold store_term.
    Exists y1 z1 y2 z2.
    entailer!.
    apply AlphaQuant.
    + rewrite H7 in H16; injection H16; intros.
      rewrite H8 in H17; injection H17; intros.
      rewrite H29, H32; exact H13.
    + right; exists str.
      rewrite <- H7, <- H8.
      auto.
Qed.

Lemma proof_of_alpha_equiv_return_wit_8_2 : alpha_equiv_return_wit_8_2.
Proof.
  pre_process.
  rewrite H, H7, H8.
  rewrite <- derivable1_orp_intros1.
  unfold store_term; fold store_term.
  Exists y1 z1 y2 z2.
  entailer!.
  contradict H0.
  inversion H0.
  destruct H34 as [Ha|Hb].
  + destruct Ha as [Hc Hd].
    admit.
  + destruct Hb as [x Hx]. 
  
  Admitted. 

Lemma proof_of_alpha_equiv_return_wit_9_1 : alpha_equiv_return_wit_9_1.
Proof. 
  pre_process.
  rewrite H.
  rewrite <- derivable1_orp_intros1.
  pose proof store_term_unfold 0 term2.
  Admitted. 

Lemma proof_of_alpha_equiv_return_wit_9_2 : alpha_equiv_return_wit_9_2.
Proof.
  pre_process.
  rewrite H.
  rewrite <- derivable1_orp_intros1.
  pose proof store_term_unfold 0 term1.
  Admitted. 

Lemma proof_of_alpha_equiv_return_wit_10 : alpha_equiv_return_wit_10.
Proof.
  pre_process.
  rewrite <- derivable1_orp_intros1.
  Admitted. 

Lemma proof_of_alpha_equiv_partial_solve_wit_16_pure : alpha_equiv_partial_solve_wit_16_pure.
Proof. 
  pre_process.
  unfold store_string, NULL.
  Intros n1 n2 n3.
  entailer!.
Qed.

Lemma proof_of_alpha_equiv_partial_solve_wit_18_pure : alpha_equiv_partial_solve_wit_18_pure.
Proof.
  pre_process.
  unfold store_string, NULL.
  Intros n1 n2 n3.
  entailer!.
Qed.

Lemma proof_of_alpha_equiv_partial_solve_wit_24_pure : alpha_equiv_partial_solve_wit_24_pure.
Proof. 
  pre_process.
  unfold store_string, NULL.
  Intros n1 n2 n3.
  entailer!.
Qed. 

Lemma proof_of_alpha_equiv_partial_solve_wit_25_pure : alpha_equiv_partial_solve_wit_25_pure.
Proof. 
  pre_process.
  unfold store_string, NULL.
  Intros n1 n2 n3.
  entailer!.
Qed. 

Lemma proof_of_alpha_equiv_which_implies_wit_1 : alpha_equiv_which_implies_wit_1.
Proof.
  pre_process.
  sep_apply store_term_unfold.
  sep_apply store_term_unfold.
  unfold NULL.
  entailer!.
Qed.

Lemma proof_of_alpha_equiv_which_implies_wit_2 : alpha_equiv_which_implies_wit_2.
Proof. 
  pre_process.
  sep_apply store_term'_Var; unfold NULL.
  Intros v1 y1.
  sep_apply store_term'_Var; unfold NULL.
  Intros v2 y2.
  Exists y2 y1 v2 v1.
  entailer!.
  + auto.
  + rewrite <- H2; auto.
  + auto.
  + auto.
Qed. 

Lemma proof_of_alpha_equiv_which_implies_wit_3 : alpha_equiv_which_implies_wit_3.
Proof.
  pre_process. 
  sep_apply store_term'_Const; unfold NULL.
  Intros ty1 c1.
  sep_apply store_term'_Const; unfold NULL.
  Intros ty2 c2.
  Exists ty2 c2 ty1 c1.
  entailer!.
  + auto.
  + rewrite <- H2; auto.
  + auto.
  + auto.
Qed.

Lemma proof_of_alpha_equiv_which_implies_wit_4 : alpha_equiv_which_implies_wit_4.
Proof.
  pre_process.
  sep_apply store_term'_Apply; unfold NULL.
  Intros ltt1 rtt1 yy1 zz1.
  sep_apply store_term'_Apply; unfold NULL.
  Intros ltt2 rtt2 yy2 zz2.
  Exists zz2 zz1 yy2 yy1.
  Exists ltt2 rtt2 ltt1 rtt1.
  entailer!.
  + auto.
  + rewrite <- H2; auto.
  + auto.
  + auto.
Qed.

Lemma proof_of_alpha_equiv_which_implies_wit_5 : alpha_equiv_which_implies_wit_5.
Proof. 
  pre_process.
  sep_apply store_term'_Quant; unfold NULL.
  Intros qtt1 qvv1 bb1 yy1 zz1.
  sep_apply store_term'_Quant; unfold NULL.
  Intros qtt2 qvv2 bb2 yy2 zz2.
  Exists zz2 zz1 yy2 yy1.
  Exists qtt2 qvv2 bb2.
  Exists qtt1 qvv1 bb1.
  entailer!.
  + auto.
  + rewrite <- H2; auto.
  + auto.
  + auto.
Qed.

Lemma proof_of_alpha_equiv_which_implies_wit_6 : alpha_equiv_which_implies_wit_6.
Proof.
  pre_process.
  rewrite H1, H2.
  unfold store_term; fold store_term.
  Exists y1 z1 y2 z2.
  entailer!.
Qed.

Lemma proof_of_alpha_equiv_which_implies_wit_7 : alpha_equiv_which_implies_wit_7.
Proof.
  pre_process.
  rewrite H in H0.
  unfold termtypeID in H, H0.
  destruct term1; try discriminate.
  destruct term2; try discriminate.
  unfold store_term; fold store_term.
  Intros yy1 zz1 yy2 zz2.
  Exists zz2 zz1 yy2 yy1.
  Exists qtype0 qvar0 term2.
  Exists qtype qvar term1.
  entailer!.
Qed. 

