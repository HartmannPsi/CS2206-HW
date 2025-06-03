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
Require Import cnf_trans_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Import naive_C_Rules.
From SimpleC.EE Require Import smt_lang_lib.
From SimpleC.EE Require Import cnf_trans_lib.
From SimpleC.EE Require Import malloc.
From SimpleC.EE Require Import super_poly_sll2.
Local Open Scope sac.

Lemma proof_of_clause_gen_unary_safety_wit_5 : clause_gen_unary_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_clause_gen_unary_safety_wit_7 : clause_gen_unary_safety_wit_7.
Proof. Admitted. 

Lemma proof_of_clause_gen_unary_safety_wit_8 : clause_gen_unary_safety_wit_8.
Proof. Admitted. 

Lemma proof_of_clause_gen_unary_return_wit_1 : clause_gen_unary_return_wit_1.
Proof.
  pre_process.
  rename H8 into H100.
  rename H9 into H200.
  rename H10 into H300.
  rename H11 into H400.
  assert ( all_zero_list 3 = 0 :: 0 :: 0 :: nil). {
    unfold all_zero_list.
    unfold all_zero_list_nat.
    unfold Z.to_nat.
    simpl; easy.
  }
  rewrite H8.
  assert ((-p2_pre) :: (-p3_pre) :: 0 :: nil = (replace_Znth 1 (- p3_pre) (replace_Znth 0 (- p2_pre) (0::0::0::nil)))). {
    unfold replace_Znth.
    unfold replace_nth.
    unfold Z.to_nat.
    simpl; easy.
  }
  rewrite <- H9.
  clear H9.
  assert ( p2_pre :: p3_pre :: 0 :: nil = (replace_Znth 1 p3_pre (replace_Znth 0 p2_pre (0 :: 0 :: 0 :: nil)))). {
    unfold replace_Znth.
    unfold replace_nth.
    unfold Z.to_nat.
    simpl; easy.
  }
  rewrite <- H9.
  clear H9 H8.
  assert (retval_3 <> NULL) by easy.
  sep_apply (store_cnf_list_fold retval_3 (p2_pre :: p3_pre :: 0 :: nil) retval).
  assert (retval_4 <> NULL) by easy.
  sep_apply (store_cnf_list_fold retval_4 (- p2_pre :: - p3_pre :: 0 :: nil) retval_2).
  pose proof @sllseg_len1 cnf_list_cell store_cnf_list_cell "cnf_list" "next".
  sep_apply (H12 retval_3 (p2_pre :: p3_pre :: 0 :: nil) retval_4).
  sep_apply (H12 retval_4 (- p2_pre :: - p3_pre :: 0 :: nil) y).
  clear H12 H13 H14.
  pose proof @sllseg_sll cnf_list_cell store_cnf_list_cell "cnf_list" "next".
  unfold sll_cnf_list.
  specialize (H12 retval_4 y ((- p2_pre :: - p3_pre :: 0 :: nil) :: nil) clist).
  pose proof derivable1_sepcon_comm.
  pose proof derivable1_sepcon_assoc1.
  entailer!.
  sep_apply H12.
  clear H12.
  pose proof @sllseg_sll cnf_list_cell store_cnf_list_cell "cnf_list" "next".
  specialize (H12 retval_3 retval_4 ((p2_pre :: p3_pre :: 0 :: nil) :: nil)(((- p2_pre :: - p3_pre :: 0 :: nil) :: nil) ++ clist)).
  repeat rewrite H14.
  rewrite (H13 (sll store_cnf_list_cell "cnf_list" "next" retval_4 (((- p2_pre :: - p3_pre :: 0 :: nil) :: nil) ++ clist)) _).
  sep_apply H12.
  clear H12.
  unfold iff2cnf_unary.
  unfold store_predata.
  Exists retval_3.
  entailer!.
  unfold sll_cnf_list.
  assert ((((p2_pre :: p3_pre :: 0 :: nil) :: nil) ++ ((- p2_pre :: - p3_pre :: 0 :: nil) :: nil) ++ clist) = (((p2_pre :: p3_pre :: 0 :: nil) :: (- p2_pre :: - p3_pre :: 0 :: nil) :: nil) ++ clist)). {
    easy.
  }
  rewrite <- H12.
  repeat rewrite H14.
  3: easy.
  3: easy.
  3: easy.
  3: easy.
  2: {
    pose proof app_comm_cons.
    rewrite <- H12.
    pose proof Zlength_cons.
    rewrite H15.
    unfold app.
    rewrite H15.
    lia.
  }
  1: {
    pose proof prop_cnt_nneg clist.
    assert (pcnt >= 1) by lia.
    assert (prop_cnt_inf clist <= pcnt - 1) by lia.
    unfold prop_cnt_inf in H17.
    pose proof Z.max_lub_l _ _ _ H17.
    pose proof Z.max_lub_r _ _ _ H17.
    (* Search (Z.max _ _ <= _). *)
    unfold prop_cnt_inf.
    apply Z.max_lub.
    + simpl.
      repeat apply Z.max_lub; try lia.
    + simpl.
      (* Search (Z.abs _ <= _). *)
      apply Z.abs_le.
      split.
      - Search (_ <= Z.min _ _).
        repeat apply Z.min_glb; try lia.
      - Search (Z.min _ _ <= _).
        pose proof Z.le_min_l (Z.min p2_pre (Z.min p3_pre (Z.min 0 0))) (Z.min (Z.min (- p2_pre) (Z.min (- p3_pre) (Z.min 0 0))) (min_cnf clist)).
        pose proof Z.le_min_l p2_pre (Z.min p3_pre (Z.min 0 0)).
        remember (Z.min (Z.min p2_pre (Z.min p3_pre (Z.min 0 0)))
        (Z.min (Z.min (- p2_pre) (Z.min (- p3_pre) (Z.min 0 0))) (min_cnf clist))) as tmp2 eqn:H2000.
        remember (Z.min p2_pre (Z.min p3_pre (Z.min 0 0))) as tmp1 eqn:H1000.
        clear H1000 H2000.
        lia.
  }
Qed.

Lemma proof_of_clause_gen_unary_which_implies_wit_1 : clause_gen_unary_which_implies_wit_1.
Proof. Admitted. 

Lemma proof_of_clause_gen_binary_safety_wit_5 : clause_gen_binary_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_clause_gen_binary_safety_wit_8 : clause_gen_binary_safety_wit_8.
Proof. Admitted. 

Lemma proof_of_clause_gen_binary_safety_wit_13 : clause_gen_binary_safety_wit_13.
Proof. Admitted. 

Lemma proof_of_clause_gen_binary_safety_wit_16 : clause_gen_binary_safety_wit_16.
Proof. Admitted. 

Lemma proof_of_clause_gen_binary_safety_wit_24 : clause_gen_binary_safety_wit_24.
Proof. Admitted. 

Lemma proof_of_clause_gen_binary_safety_wit_27 : clause_gen_binary_safety_wit_27.
Proof. Admitted. 

Lemma proof_of_clause_gen_binary_safety_wit_29 : clause_gen_binary_safety_wit_29.
Proof. Admitted. 

Lemma proof_of_clause_gen_binary_safety_wit_31 : clause_gen_binary_safety_wit_31.
Proof. Admitted. 

Lemma proof_of_clause_gen_binary_safety_wit_34 : clause_gen_binary_safety_wit_34.
Proof. Admitted. 

Lemma proof_of_clause_gen_binary_safety_wit_44 : clause_gen_binary_safety_wit_44.
Proof. Admitted. 

Lemma proof_of_clause_gen_binary_safety_wit_47 : clause_gen_binary_safety_wit_47.
Proof. Admitted. 

Lemma proof_of_clause_gen_binary_safety_wit_50 : clause_gen_binary_safety_wit_50.
Proof. Admitted. 

Lemma proof_of_clause_gen_binary_safety_wit_61 : clause_gen_binary_safety_wit_61.
Proof. Admitted. 

Lemma proof_of_clause_gen_binary_safety_wit_63 : clause_gen_binary_safety_wit_63.
Proof. Admitted. 

Lemma proof_of_clause_gen_binary_safety_wit_67 : clause_gen_binary_safety_wit_67.
Proof. Admitted. 

Lemma proof_of_clause_gen_binary_safety_wit_69 : clause_gen_binary_safety_wit_69.
Proof. Admitted. 

Lemma proof_of_clause_gen_binary_safety_wit_71 : clause_gen_binary_safety_wit_71.
Proof. Admitted. 

Lemma proof_of_clause_gen_binary_safety_wit_74 : clause_gen_binary_safety_wit_74.
Proof. Admitted. 

Lemma proof_of_clause_gen_binary_safety_wit_98 : clause_gen_binary_safety_wit_98.
Proof. Admitted. 

Lemma proof_of_clause_gen_binary_safety_wit_100 : clause_gen_binary_safety_wit_100.
Proof. Admitted. 

Lemma proof_of_clause_gen_binary_safety_wit_130 : clause_gen_binary_safety_wit_130.
Proof. Admitted. 

Lemma proof_of_clause_gen_binary_safety_wit_132 : clause_gen_binary_safety_wit_132.
Proof. Admitted. 

Lemma proof_of_clause_gen_binary_safety_wit_134 : clause_gen_binary_safety_wit_134.
Proof. Admitted. 

Lemma proof_of_clause_gen_binary_safety_wit_136 : clause_gen_binary_safety_wit_136.
Proof. Admitted. 

Lemma proof_of_clause_gen_binary_safety_wit_138 : clause_gen_binary_safety_wit_138.
Proof. Admitted. 

Lemma proof_of_clause_gen_binary_safety_wit_140 : clause_gen_binary_safety_wit_140.
Proof. Admitted. 

Lemma proof_of_clause_gen_binary_safety_wit_142 : clause_gen_binary_safety_wit_142.
Proof. Admitted. 

Lemma proof_of_clause_gen_binary_return_wit_1_1 : clause_gen_binary_return_wit_1_1.
Proof. Admitted. 

Lemma proof_of_clause_gen_binary_return_wit_1_2 : clause_gen_binary_return_wit_1_2.
Proof. Admitted. 

Lemma proof_of_clause_gen_binary_return_wit_1_3 : clause_gen_binary_return_wit_1_3.
Proof. Admitted. 

Lemma proof_of_clause_gen_binary_return_wit_1_4 : clause_gen_binary_return_wit_1_4.
Proof. Admitted. 

Lemma proof_of_clause_gen_binary_return_wit_1_5 : clause_gen_binary_return_wit_1_5.
Proof. Admitted. 

Lemma proof_of_clause_gen_binary_return_wit_1_6 : clause_gen_binary_return_wit_1_6.
Proof. Admitted. 

Lemma proof_of_clause_gen_binary_return_wit_1_7 : clause_gen_binary_return_wit_1_7.
Proof. Admitted. 

Lemma proof_of_clause_gen_binary_return_wit_1_8 : clause_gen_binary_return_wit_1_8.
Proof. Admitted. 

Lemma proof_of_clause_gen_binary_return_wit_1_9 : clause_gen_binary_return_wit_1_9.
Proof. Admitted. 

Lemma proof_of_clause_gen_binary_which_implies_wit_1 : clause_gen_binary_which_implies_wit_1.
Proof. Admitted. 

Lemma proof_of_prop2cnf_safety_wit_3 : prop2cnf_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_prop2cnf_safety_wit_6 : prop2cnf_safety_wit_6.
Proof. Admitted. 

Lemma proof_of_prop2cnf_safety_wit_9 : prop2cnf_safety_wit_9.
Proof. Admitted. 

Lemma proof_of_prop2cnf_return_wit_1_1 : prop2cnf_return_wit_1_1.
Proof. Admitted. 

Lemma proof_of_prop2cnf_return_wit_1_2 : prop2cnf_return_wit_1_2.
Proof. Admitted. 

Lemma proof_of_prop2cnf_return_wit_1_3 : prop2cnf_return_wit_1_3.
Proof. Admitted. 

Lemma proof_of_prop2cnf_partial_solve_wit_5_pure : prop2cnf_partial_solve_wit_5_pure.
Proof. Admitted. 

Lemma proof_of_prop2cnf_partial_solve_wit_10_pure : prop2cnf_partial_solve_wit_10_pure.
Proof. Admitted. 

Lemma proof_of_prop2cnf_partial_solve_wit_18_pure : prop2cnf_partial_solve_wit_18_pure.
Proof. Admitted. 

Lemma proof_of_prop2cnf_which_implies_wit_1 : prop2cnf_which_implies_wit_1.
Proof. Admitted. 

Lemma proof_of_prop2cnf_which_implies_wit_2 : prop2cnf_which_implies_wit_2.
Proof. Admitted. 

Lemma proof_of_prop2cnf_which_implies_wit_3 : prop2cnf_which_implies_wit_3.
Proof. Admitted. 

Lemma proof_of_prop2cnf_which_implies_wit_4 : prop2cnf_which_implies_wit_4.
Proof. Admitted. 

Lemma proof_of_prop2cnf_which_implies_wit_6 : prop2cnf_which_implies_wit_6.
Proof. Admitted. 

Lemma proof_of_prop2cnf_which_implies_wit_8 : prop2cnf_which_implies_wit_8.
Proof. Admitted. 

Lemma proof_of_prop2cnf_which_implies_wit_9 : prop2cnf_which_implies_wit_9.
Proof. Admitted. 

Lemma proof_of_prop2cnf_which_implies_wit_10 : prop2cnf_which_implies_wit_10.
Proof. Admitted. 

Lemma proof_of_prop2cnf_which_implies_wit_12 : prop2cnf_which_implies_wit_12.
Proof. Admitted. 

Lemma proof_of_prop2cnf_which_implies_wit_14 : prop2cnf_which_implies_wit_14.
Proof. Admitted. 

