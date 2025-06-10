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
  unfold list_Z_cmp in H0.
  destruct (list_Z_eqb str1 str2) eqn:Heq; [ contradiction | ].
  unfold store_term, term_eqn, term_eqb.
  rewrite H3, H4.
  Exists y z.
  entailer!.
  rewrite Heq.
  reflexivity.
Qed.

Lemma proof_of_alpha_equiv_return_wit_1_2 : alpha_equiv_return_wit_1_2.
Proof.
  pre_process.
  rewrite H in H0.
  unfold list_Z_cmp in H0.
  destruct (list_Z_eqb str1 str2) eqn:Heq; [ | discriminate ].
  unfold store_term, term_eqn, term_eqb.
  rewrite H3, H4.
  Exists y z.
  entailer!.
  rewrite Heq.
  reflexivity.
Qed.

Lemma proof_of_alpha_equiv_return_wit_2 : alpha_equiv_return_wit_2.
Proof.
  pre_process.
  unfold store_term, term_eqn, term_eqb.
  rewrite H2, H3.
  entailer!.
  destruct (ctID typ1 =? ctID typ2)%Z eqn:E.
  + apply Z.eqb_eq in E.
    contradiction.
  + rewrite Bool.andb_false_l.
    reflexivity.
Qed.

Lemma proof_of_alpha_equiv_return_wit_3_1 : alpha_equiv_return_wit_3_1.
Proof. 
  pre_process.
  unfold store_term.
  rewrite H4, H5.
  entailer!.
  unfold term_eqn, term_eqb.
  rewrite H1 at 1.
  rewrite Z.eqb_refl.
  rewrite Bool.andb_true_l.
  destruct (con1 =? con2)%Z eqn:E.
  + apply Z.eqb_eq in E.
    contradiction.
  + unfold negb.
    rewrite H0.
    reflexivity.
Qed.

Lemma proof_of_alpha_equiv_return_wit_3_2 : alpha_equiv_return_wit_3_2.
Proof.
  pre_process.
  unfold store_term.
  rewrite H4, H5.
  entailer!.
  unfold term_eqn, term_eqb.
  rewrite H1 at 1.
  rewrite Z.eqb_refl.
  rewrite Bool.andb_true_l.
  destruct (con1 =? con2)%Z eqn:E.
  + unfold negb.
    rewrite H0.
    reflexivity. 
  + apply Z.eqb_neq in E.
    contradiction.
Qed.

Lemma proof_of_alpha_equiv_return_wit_4 : alpha_equiv_return_wit_4.
Proof.
  pre_process.
  unfold store_term.
  rewrite H3, H4.
  entailer!.
  unfold term_eqn, term_eqb.
  rewrite H0 at 1.
  rewrite Z.eqb_refl.
  rewrite Bool.andb_true_l.
  destruct (con1 =? con2)%Z eqn:E.
  + unfold negb.
    destruct (ctID typ1 =? 0)%Z eqn:Eq; [ | reflexivity].
    apply Z.eqb_eq in E, Eq.
    contradiction.
  + unfold negb.
    apply Z.eqb_neq in E.
    destruct (ctID typ1 =? 0)%Z eqn:Eq; [ | reflexivity].
    apply Z.eqb_eq in Eq.
    contradiction.
Qed.  

Lemma proof_of_alpha_equiv_return_wit_5_1 : alpha_equiv_return_wit_5_1.
Proof.
  pre_process.
  unfold store_term.
  rewrite H5, H6.
  fold store_term.
  Exists y1 z1 y2 z2.
  entailer!.
  unfold term_eqn in *.
  unfold term_eqb.
  fold term_eqb.
  destruct (term_eqb rt1 rt2) eqn:Eqr; [ | contradiction].
  destruct (term_eqb lt1 lt2) eqn:Eql; [ | contradiction].
  reflexivity.
Qed.

Lemma proof_of_alpha_equiv_return_wit_5_2 : alpha_equiv_return_wit_5_2.
Proof.
  pre_process.
  unfold store_term.
  rewrite H5, H6.
  fold store_term.
  Exists y1 z1 y2 z2.
  entailer!.
  unfold term_eqn in *.
  unfold term_eqb.
  fold term_eqb.
  destruct (term_eqb lt1 lt2) eqn:Eql; [ | contradiction].
  destruct (term_eqb rt1 rt2) eqn:Eqr; [ | reflexivity].
  congruence.
Qed.

Lemma proof_of_alpha_equiv_return_wit_5_3 : alpha_equiv_return_wit_5_3.
Proof.
  pre_process.
  unfold store_term.
  rewrite H3, H4.
  fold store_term.
  Exists y1 z1 y2 z2.
  entailer!.
  unfold term_eqn in *.
  unfold term_eqb.
  fold term_eqb.
  destruct (term_eqb lt1 lt2) eqn:Eql; [ | reflexivity].
  congruence.
Qed.

Lemma proof_of_alpha_equiv_return_wit_6 : alpha_equiv_return_wit_6.
Proof.
  pre_process.
  unfold store_term.
  rewrite H2, H3.
  fold store_term.
  Exists y1 z1 y2 z2.
  entailer!.
  unfold term_eqn in *.
  unfold term_eqb.
  fold term_eqb.
  destruct (qtID qt1 =? qtID qt2)%Z eqn:Eq; [ | reflexivity].
  apply Z.eqb_eq in Eq.
  congruence.
Qed.

Lemma proof_of_alpha_equiv_return_wit_7 : alpha_equiv_return_wit_7.
Proof.
  pre_process.
  unfold store_term.
  rewrite H5, H6.
  fold store_term.
  Exists y1 z1 y2 z2.
  entailer!.
  unfold term_eqn in *.
  unfold term_eqb.
  fold term_eqb.
  rewrite H0 in H1. 
  unfold list_Z_cmp in H1.
  destruct (qtID qt1 =? qtID qt2)%Z eqn:Eq.
  + destruct (list_Z_eqb qv1 qv2) eqn:vEq; [ | congruence].
    rewrite Bool.andb_true_l.
    tauto.
  + destruct (list_Z_eqb qv1 qv2) eqn:vEq; [ | congruence].
    rewrite Z.eqb_neq in Eq.
    congruence.
Qed.

Lemma proof_of_alpha_equiv_return_wit_8 : alpha_equiv_return_wit_8.
Proof.
  pre_process.
  unfold store_term.
  rewrite H9, H10.
  fold store_term.
  Exists y1 z1 y2 z2.
  entailer!.  
  unfold term_eqn in *.
  unfold term_eqb.
  fold term_eqb.
  Admitted. 

Lemma proof_of_alpha_equiv_return_wit_9_1 : alpha_equiv_return_wit_9_1.
Proof. Admitted. 

Lemma proof_of_alpha_equiv_return_wit_9_2 : alpha_equiv_return_wit_9_2.
Proof. Admitted. 

Lemma proof_of_alpha_equiv_return_wit_10 : alpha_equiv_return_wit_10.
Proof. Admitted. 

Lemma proof_of_alpha_equiv_which_implies_wit_1 : alpha_equiv_which_implies_wit_1.
Proof. Admitted. 

Lemma proof_of_alpha_equiv_which_implies_wit_2 : alpha_equiv_which_implies_wit_2.
Proof. Admitted. 

Lemma proof_of_alpha_equiv_which_implies_wit_3 : alpha_equiv_which_implies_wit_3.
Proof. Admitted. 

Lemma proof_of_alpha_equiv_which_implies_wit_4 : alpha_equiv_which_implies_wit_4.
Proof. Admitted. 

Lemma proof_of_alpha_equiv_which_implies_wit_5 : alpha_equiv_which_implies_wit_5.
Proof. Admitted. 

Lemma proof_of_alpha_equiv_which_implies_wit_6 : alpha_equiv_which_implies_wit_6.
Proof. Admitted. 

