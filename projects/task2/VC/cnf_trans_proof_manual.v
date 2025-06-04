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
Proof.
  pre_process.
  unfold store_predata.
  Intros y.
  Exists y.
  entailer!.
Qed.

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

Lemma proof_of_clause_gen_binary_safety_wit_80 : clause_gen_binary_safety_wit_80.
Proof. Admitted. 

Lemma proof_of_clause_gen_binary_safety_wit_97 : clause_gen_binary_safety_wit_97.
Proof. Admitted. 

Lemma proof_of_clause_gen_binary_safety_wit_99 : clause_gen_binary_safety_wit_99.
Proof. Admitted. 

Lemma proof_of_clause_gen_binary_safety_wit_125 : clause_gen_binary_safety_wit_125.
Proof. Admitted. 

Lemma proof_of_clause_gen_binary_safety_wit_127 : clause_gen_binary_safety_wit_127.
Proof. Admitted. 

Lemma proof_of_clause_gen_binary_safety_wit_129 : clause_gen_binary_safety_wit_129.
Proof. Admitted. 

Lemma proof_of_clause_gen_binary_safety_wit_131 : clause_gen_binary_safety_wit_131.
Proof. Admitted. 

Lemma proof_of_clause_gen_binary_safety_wit_133 : clause_gen_binary_safety_wit_133.
Proof. Admitted. 

Lemma proof_of_clause_gen_binary_safety_wit_135 : clause_gen_binary_safety_wit_135.
Proof. Admitted. 

Lemma proof_of_clause_gen_binary_return_wit_1_1 : clause_gen_binary_return_wit_1_1.
Proof.
  pre_process.
  rewrite all_zero_list_3.
  repeat rewrite replace_0th.
  repeat rewrite replace_1st.
  repeat rewrite replace_2nd.
  pose proof store_cnf_list_fold.
  sep_apply (H28 retval_8 (- p1_pre :: p2_pre :: - p3_pre :: nil) retval_4); try easy.
  sep_apply (H28 retval_7 (p1_pre :: - p2_pre :: - p3_pre :: nil) retval_3); try easy.
  sep_apply (H28 retval_6 (- p1_pre :: - p2_pre :: p3_pre :: nil) retval_2); try easy.
  sep_apply (H28 retval_5 (p1_pre :: p2_pre :: p3_pre :: nil) retval); try easy.
  clear H28.
  pose proof @sllseg_len1 cnf_list_cell store_cnf_list_cell "cnf_list" "next".
  sep_apply (H28 retval_6 (- p1_pre :: - p2_pre :: p3_pre :: nil) retval_7); try easy.
  sep_apply (H28 retval_7 (p1_pre :: - p2_pre :: - p3_pre :: nil) retval_8); try easy.
  sep_apply (H28 retval_8 (- p1_pre :: p2_pre :: - p3_pre :: nil) y); try easy.
  sep_apply (H28 retval_5 (p1_pre :: p2_pre :: p3_pre :: nil) retval_6); try easy.
  clear H28.
  pose proof @sllseg_sll cnf_list_cell store_cnf_list_cell "cnf_list" "next".
  unfold sll_cnf_list.
  sep_apply (H28 retval_8 y ((- p1_pre :: p2_pre :: - p3_pre :: nil) :: nil) clist); try easy.
  sep_apply (H28 retval_7 retval_8 ((p1_pre :: - p2_pre :: - p3_pre :: nil) :: nil) (((- p1_pre :: p2_pre :: - p3_pre :: nil) :: nil) ++ clist)); try easy.
  sep_apply (H28 retval_6 retval_7 ((- p1_pre :: - p2_pre :: p3_pre :: nil) :: nil) (((p1_pre :: - p2_pre :: - p3_pre :: nil) :: nil) ++
  ((- p1_pre :: p2_pre :: - p3_pre :: nil) :: nil) ++ clist)); try easy.
  sep_apply (H28 retval_5 retval_6 ((p1_pre :: p2_pre :: p3_pre :: nil) :: nil) (((- p1_pre :: - p2_pre :: p3_pre :: nil) :: nil) ++
  ((p1_pre :: - p2_pre :: - p3_pre :: nil) :: nil) ++ ((- p1_pre :: p2_pre :: - p3_pre :: nil) :: nil) ++ clist)); try easy.
  unfold store_predata.
  Exists retval_5.
  assert (bop = SMTPROP_IFF). {
    destruct bop; unfold SmtPBID in *; try contradiction.
    reflexivity.
  }
  rewrite H37.
  unfold iff2cnf_length_binary, iff2cnf_binary.
  destruct (p1_pre ==? p2_pre); try contradiction.
  assert (Zlength
  (((p1_pre :: p2_pre :: p3_pre :: nil)
    :: (- p1_pre :: - p2_pre :: p3_pre :: nil)
       :: (p1_pre :: - p2_pre :: - p3_pre :: nil)
          :: (- p1_pre :: p2_pre :: - p3_pre :: nil) :: nil) ++ clist) = 
              ccnt + 4). {
    pose proof app_comm_cons.
    repeat rewrite <- H38.
    pose proof Zlength_cons.
    repeat rewrite H39.
    unfold app.
    rewrite H3.
    lia.
  }
  rewrite H38.
  clear H38 H28 H H0 H1 H24 H25 H26.
  assert (prop_cnt_inf
  (((p1_pre :: p2_pre :: p3_pre :: nil)
    :: (- p1_pre :: - p2_pre :: p3_pre :: nil)
       :: (p1_pre :: - p2_pre :: - p3_pre :: nil)
          :: (- p1_pre :: p2_pre :: - p3_pre :: nil) :: nil) ++ clist) <= pcnt). {
    pose proof prop_cnt_nneg clist.
    clear H29 H30 H31 H32 H33 H34 H35 H36.
    assert (pcnt >= 1) by lia.
    assert (prop_cnt_inf clist <= pcnt - 1) by lia.
    unfold prop_cnt_inf in H1.
    pose proof Z.max_lub_l _ _ _ H1.
    pose proof Z.max_lub_r _ _ _ H1.
    (* Search (Z.max _ _ <= _). *)
    unfold prop_cnt_inf.
    apply Z.max_lub.
    + simpl.
      repeat apply Z.max_lub; try lia.
    + simpl.
      (* Search (Z.abs _ <= _). *)
      apply Z.abs_le.
      split.
      - (*Search (_ <= Z.min _ _). *)
        repeat apply Z.min_glb; try lia.
      - (*Search (Z.min _ _ <= _). *)
        pose proof Z.le_min_l (Z.min p1_pre (Z.min p2_pre (Z.min p3_pre 0))) (Z.min (Z.min (- p1_pre) (Z.min (- p2_pre) (Z.min p3_pre 0)))
        (Z.min (Z.min p1_pre (Z.min (- p2_pre) (Z.min (- p3_pre) 0)))
           (Z.min (Z.min (- p1_pre) (Z.min p2_pre (Z.min (- p3_pre) 0))) (min_cnf clist)))).
        pose proof Z.le_min_l p1_pre (Z.min p2_pre (Z.min p3_pre 0)).
        remember (Z.min (Z.min p1_pre (Z.min p2_pre (Z.min p3_pre 0)))
        (Z.min (Z.min (- p1_pre) (Z.min (- p2_pre) (Z.min p3_pre 0)))
           (Z.min (Z.min p1_pre (Z.min (- p2_pre) (Z.min (- p3_pre) 0)))
              (Z.min (Z.min (- p1_pre) (Z.min p2_pre (Z.min (- p3_pre) 0))) (min_cnf clist))))) as tmp2 eqn:H2000.
        remember (Z.min p1_pre (Z.min p2_pre (Z.min p3_pre 0))) as tmp1 eqn:H1000.
        clear H1000 H2000.
        lia.
  }
  repeat rewrite <- app_comm_cons.
  unfold app.
  clear - H H2.
  entailer!.
Qed.

Lemma proof_of_clause_gen_binary_return_wit_1_2 : clause_gen_binary_return_wit_1_2.
Proof.
  pre_process.
  rewrite all_zero_list_3.
  repeat rewrite replace_0th.
  repeat rewrite replace_1st.
  repeat rewrite replace_2nd.
  assert (bop = SMTPROP_OR). {
    destruct bop; unfold SmtPBID in *; try contradiction; try lia.
    reflexivity.
  }
  clear H23 H24.
  remember ((p1_pre :: - p3_pre :: 0 :: nil)) as c1 eqn:H_c1.
  remember ((- p2_pre :: p3_pre :: 0 :: nil)) as c2 eqn:H_c2.
  remember ((- p1_pre :: p3_pre :: 0 :: nil)) as c3 eqn:H_c3.
  pose proof store_cnf_list_fold.
  sep_apply (H23 retval_7 c1 retval_3); try easy.
  sep_apply (H23 retval_6 c2 retval_2); try easy.
  sep_apply (H23 retval_5 c3 retval); try easy.
  clear H23.
  pose proof @sllseg_len1 cnf_list_cell store_cnf_list_cell "cnf_list" "next".
  sep_apply (H23 retval_5 c3 retval_6); try easy.
  sep_apply (H23 retval_6 c2 retval_7); try easy.
  sep_apply (H23 retval_7 c1 y); try easy.
  clear H23.
  pose proof @sllseg_sll cnf_list_cell store_cnf_list_cell "cnf_list" "next".
  unfold sll_cnf_list.
  sep_apply (H23 retval_7 y (c1 :: nil) clist); try easy.
  sep_apply (H23 retval_6 retval_7 (c2 :: nil) ((c1 :: nil) ++ clist)); try easy.
  sep_apply (H23 retval_5 retval_6 (c3 :: nil) ((c2 :: nil) ++ (c1 :: nil) ++ clist)); try easy.
  clear H23.
  unfold store_predata.
  Exists retval_5.
  rewrite H25.
  unfold iff2cnf_length_binary, iff2cnf_binary.
  destruct (p1_pre ==? p2_pre); try contradiction.
  repeat rewrite <- app_comm_cons.
  unfold app.
  rewrite <- H_c1, <- H_c2, <- H_c3.
  assert (Zlength (c3 :: c2 :: c1 :: clist) = ccnt + 3). {
    repeat rewrite Zlength_cons.
    rewrite H3.
    lia.
  }
  rewrite H23.
  assert (prop_cnt_inf (c3 :: c2 :: c1 :: clist) <= pcnt). {
    pose proof prop_cnt_nneg clist.
    clear H24 H26 H27 H28 H29 H30.
    assert (pcnt >= 1) by lia.
    assert (prop_cnt_inf clist <= pcnt - 1) by lia.
    unfold prop_cnt_inf in H26.
    pose proof Z.max_lub_l _ _ _ H26.
    pose proof Z.max_lub_r _ _ _ H26.
    (* Search (Z.max _ _ <= _). *)
    rewrite H_c1, H_c2, H_c3.
    unfold prop_cnt_inf.
    apply Z.max_lub.
    + simpl.
      repeat apply Z.max_lub; try lia.
    + simpl.
      (* Search (Z.abs _ <= _). *)
      apply Z.abs_le.
      split.
      - (*Search (_ <= Z.min _ _). *)
        repeat apply Z.min_glb; try lia.
      - (*Search (Z.min _ _ <= _). *)
        pose proof Z.le_min_l (Z.min (- p1_pre) (Z.min p3_pre (Z.min 0 0))) (Z.min (Z.min (- p2_pre) (Z.min p3_pre (Z.min 0 0)))
        (Z.min (Z.min p1_pre (Z.min (- p3_pre) (Z.min 0 0))) (min_cnf clist))).
        pose proof Z.le_min_l (- p1_pre) (Z.min p3_pre (Z.min 0 0)).
        remember (Z.min (Z.min (- p1_pre) (Z.min p3_pre (Z.min 0 0)))
        (Z.min (Z.min (- p2_pre) (Z.min p3_pre (Z.min 0 0)))
           (Z.min (Z.min p1_pre (Z.min (- p3_pre) (Z.min 0 0))) (min_cnf clist)))) as tmp2 eqn:H2000.
        remember (Z.min (- p1_pre) (Z.min p3_pre (Z.min 0 0))) as tmp1 eqn:H1000.
        clear H1000 H2000.
        lia.
  }
  clear - H2 H31.
  entailer!.
Qed.

Lemma proof_of_clause_gen_binary_return_wit_1_3 : clause_gen_binary_return_wit_1_3.
Proof.
  pre_process.
  rewrite all_zero_list_3.
  repeat rewrite replace_0th.
  repeat rewrite replace_1st.
  repeat rewrite replace_2nd.
  assert (bop = SMTPROP_OR). {
    destruct bop; unfold SmtPBID in *; try contradiction; try lia.
    reflexivity.
  }
  clear H23 H24.
  remember (p1_pre :: p2_pre :: - p3_pre :: nil) as c1 eqn:H_c1.
  remember (- p2_pre :: p3_pre :: 0 :: nil) as c2 eqn:H_c2.
  remember (- p1_pre :: p3_pre :: 0 :: nil) as c3 eqn:H_c3.
  pose proof store_cnf_list_fold.
  sep_apply (H23 retval_7 c1 retval_3); try easy.
  sep_apply (H23 retval_6 c2 retval_2); try easy.
  sep_apply (H23 retval_5 c3 retval); try easy.
  clear H23.
  pose proof @sllseg_len1 cnf_list_cell store_cnf_list_cell "cnf_list" "next".
  sep_apply (H23 retval_5 c3 retval_6); try easy.
  sep_apply (H23 retval_6 c2 retval_7); try easy.
  sep_apply (H23 retval_7 c1 y); try easy.
  clear H23.
  pose proof @sllseg_sll cnf_list_cell store_cnf_list_cell "cnf_list" "next".
  unfold sll_cnf_list.
  sep_apply (H23 retval_7 y (c1 :: nil) clist); try easy.
  sep_apply (H23 retval_6 retval_7 (c2 :: nil) ((c1 :: nil) ++ clist)); try easy.
  sep_apply (H23 retval_5 retval_6 (c3 :: nil) ((c2 :: nil) ++ (c1 :: nil) ++ clist)); try easy.
  clear H23.
  unfold store_predata.
  Exists retval_5.
  rewrite H25.
  unfold iff2cnf_length_binary, iff2cnf_binary.
  destruct (p1_pre ==? p2_pre); try contradiction.
  repeat rewrite <- app_comm_cons.
  unfold app.
  rewrite <- H_c1, <- H_c2, <- H_c3.
  assert (Zlength (c3 :: c2 :: c1 :: clist) = ccnt + 3). {
    repeat rewrite Zlength_cons.
    rewrite H3.
    lia.
  }
  rewrite H23.
  assert (prop_cnt_inf (c3 :: c2 :: c1 :: clist) <= pcnt). {
    pose proof prop_cnt_nneg clist.
    clear H24 H26 H27 H28 H29 H30.
    assert (pcnt >= 1) by lia.
    assert (prop_cnt_inf clist <= pcnt - 1) by lia.
    unfold prop_cnt_inf in H26.
    pose proof Z.max_lub_l _ _ _ H26.
    pose proof Z.max_lub_r _ _ _ H26.
    (* Search (Z.max _ _ <= _). *)
    rewrite H_c1, H_c2, H_c3.
    unfold prop_cnt_inf.
    apply Z.max_lub.
    + simpl.
      repeat apply Z.max_lub; try lia.
    + simpl.
      (* Search (Z.abs _ <= _). *)
      apply Z.abs_le.
      split.
      - (*Search (_ <= Z.min _ _). *)
        repeat apply Z.min_glb; try lia.
      - (*Search (Z.min _ _ <= _). *)
        pose proof Z.le_min_l (Z.min (- p1_pre) (Z.min p3_pre (Z.min 0 0)))
        (Z.min (Z.min (- p2_pre) (Z.min p3_pre (Z.min 0 0)))
           (Z.min (Z.min p1_pre (Z.min p2_pre (Z.min (- p3_pre) 0))) (min_cnf clist))).
        pose proof Z.le_min_l (- p1_pre) (Z.min p3_pre (Z.min 0 0)).
        remember (Z.min (Z.min (- p1_pre) (Z.min p3_pre (Z.min 0 0)))
        (Z.min (Z.min (- p2_pre) (Z.min p3_pre (Z.min 0 0)))
           (Z.min (Z.min p1_pre (Z.min p2_pre (Z.min (- p3_pre) 0))) (min_cnf clist)))) as tmp2 eqn:H2000.
        remember (Z.min (- p1_pre) (Z.min p3_pre (Z.min 0 0))) as tmp1 eqn:H1000.
        clear H1000 H2000.
        lia.
  }
  clear - H2 H31.
  entailer!.
Qed.

Lemma proof_of_clause_gen_binary_return_wit_1_4 : clause_gen_binary_return_wit_1_4.
Proof.
  pre_process.
  clear H24.
  rename H25 into H24.
  rewrite all_zero_list_3.
  repeat rewrite replace_0th.
  repeat rewrite replace_1st.
  repeat rewrite replace_2nd.
  assert (bop = SMTPROP_AND). {
    destruct bop; unfold SmtPBID in *; try contradiction; try lia.
    reflexivity.
  }
  clear H23 H24.
  remember (- p1_pre :: p3_pre :: 0 :: nil) as c1 eqn:H_c1.
  remember (p2_pre :: - p3_pre :: 0 :: nil) as c2 eqn:H_c2.
  remember (p1_pre :: - p3_pre :: 0 :: nil) as c3 eqn:H_c3.
  pose proof store_cnf_list_fold.
  sep_apply (H23 retval_7 c1 retval_3); try easy.
  sep_apply (H23 retval_6 c2 retval_2); try easy.
  sep_apply (H23 retval_5 c3 retval); try easy.
  clear H23.
  pose proof @sllseg_len1 cnf_list_cell store_cnf_list_cell "cnf_list" "next".
  sep_apply (H23 retval_5 c3 retval_6); try easy.
  sep_apply (H23 retval_6 c2 retval_7); try easy.
  sep_apply (H23 retval_7 c1 y); try easy.
  clear H23.
  pose proof @sllseg_sll cnf_list_cell store_cnf_list_cell "cnf_list" "next".
  unfold sll_cnf_list.
  sep_apply (H23 retval_7 y (c1 :: nil) clist); try easy.
  sep_apply (H23 retval_6 retval_7 (c2 :: nil) ((c1 :: nil) ++ clist)); try easy.
  sep_apply (H23 retval_5 retval_6 (c3 :: nil) ((c2 :: nil) ++ (c1 :: nil) ++ clist)); try easy.
  clear H23.
  unfold store_predata.
  Exists retval_5.
  rewrite H25.
  unfold iff2cnf_length_binary, iff2cnf_binary.
  destruct (p1_pre ==? p2_pre); try contradiction.
  repeat rewrite <- app_comm_cons.
  unfold app.
  rewrite <- H_c1, <- H_c2, <- H_c3.
  assert (Zlength (c3 :: c2 :: c1 :: clist) = ccnt + 3). {
    repeat rewrite Zlength_cons.
    rewrite H3.
    lia.
  }
  rewrite H23.
  assert (prop_cnt_inf (c3 :: c2 :: c1 :: clist) <= pcnt). {
    pose proof prop_cnt_nneg clist.
    clear H24 H26 H27 H28 H29 H30.
    assert (pcnt >= 1) by lia.
    assert (prop_cnt_inf clist <= pcnt - 1) by lia.
    unfold prop_cnt_inf in H26.
    pose proof Z.max_lub_l _ _ _ H26.
    pose proof Z.max_lub_r _ _ _ H26.
    (* Search (Z.max _ _ <= _). *)
    rewrite H_c1, H_c2, H_c3.
    unfold prop_cnt_inf.
    apply Z.max_lub.
    + simpl.
      repeat apply Z.max_lub; try lia.
    + simpl.
      (* Search (Z.abs _ <= _). *)
      apply Z.abs_le.
      split.
      - (*Search (_ <= Z.min _ _). *)
        repeat apply Z.min_glb; try lia.
      - (*Search (Z.min _ _ <= _). *)
        pose proof Z.le_min_l (Z.min p1_pre (Z.min (- p3_pre) (Z.min 0 0)))
        (Z.min (Z.min p2_pre (Z.min (- p3_pre) (Z.min 0 0)))
           (Z.min (Z.min (- p1_pre) (Z.min p3_pre (Z.min 0 0))) (min_cnf clist))).
        pose proof Z.le_min_l p1_pre (Z.min (- p3_pre) (Z.min 0 0)).
        remember (Z.min (Z.min p1_pre (Z.min (- p3_pre) (Z.min 0 0)))
        (Z.min (Z.min p2_pre (Z.min (- p3_pre) (Z.min 0 0)))
           (Z.min (Z.min (- p1_pre) (Z.min p3_pre (Z.min 0 0))) (min_cnf clist)))) as tmp2 eqn:H2000.
        remember (Z.min p1_pre (Z.min (- p3_pre) (Z.min 0 0))) as tmp1 eqn:H1000.
        clear H1000 H2000.
        lia.
  }
  clear - H2 H31.
  entailer!.
Qed.

Lemma proof_of_clause_gen_binary_return_wit_1_5 : clause_gen_binary_return_wit_1_5.
Proof.
  pre_process.
  clear H24.
  rename H25 into H24.
  rewrite all_zero_list_3.
  repeat rewrite replace_0th.
  repeat rewrite replace_1st.
  repeat rewrite replace_2nd.
  assert (bop = SMTPROP_AND). {
    destruct bop; unfold SmtPBID in *; try contradiction; try lia.
    reflexivity.
  }
  clear H23 H24.
  remember (- p1_pre :: - p2_pre :: p3_pre :: nil) as c1 eqn:H_c1.
  remember (p2_pre :: - p3_pre :: 0 :: nil) as c2 eqn:H_c2.
  remember (p1_pre :: - p3_pre :: 0 :: nil) as c3 eqn:H_c3.
  pose proof store_cnf_list_fold.
  sep_apply (H23 retval_7 c1 retval_3); try easy.
  sep_apply (H23 retval_6 c2 retval_2); try easy.
  sep_apply (H23 retval_5 c3 retval); try easy.
  clear H23.
  pose proof @sllseg_len1 cnf_list_cell store_cnf_list_cell "cnf_list" "next".
  sep_apply (H23 retval_5 c3 retval_6); try easy.
  sep_apply (H23 retval_6 c2 retval_7); try easy.
  sep_apply (H23 retval_7 c1 y); try easy.
  clear H23.
  pose proof @sllseg_sll cnf_list_cell store_cnf_list_cell "cnf_list" "next".
  unfold sll_cnf_list.
  sep_apply (H23 retval_7 y (c1 :: nil) clist); try easy.
  sep_apply (H23 retval_6 retval_7 (c2 :: nil) ((c1 :: nil) ++ clist)); try easy.
  sep_apply (H23 retval_5 retval_6 (c3 :: nil) ((c2 :: nil) ++ (c1 :: nil) ++ clist)); try easy.
  clear H23.
  unfold store_predata.
  Exists retval_5.
  rewrite H25.
  unfold iff2cnf_length_binary, iff2cnf_binary.
  destruct (p1_pre ==? p2_pre); try contradiction.
  repeat rewrite <- app_comm_cons.
  unfold app.
  rewrite <- H_c1, <- H_c2, <- H_c3.
  assert (Zlength (c3 :: c2 :: c1 :: clist) = ccnt + 3). {
    repeat rewrite Zlength_cons.
    rewrite H3.
    lia.
  }
  rewrite H23.
  assert (prop_cnt_inf (c3 :: c2 :: c1 :: clist) <= pcnt). {
    pose proof prop_cnt_nneg clist.
    clear H24 H26 H27 H28 H29 H30.
    assert (pcnt >= 1) by lia.
    assert (prop_cnt_inf clist <= pcnt - 1) by lia.
    unfold prop_cnt_inf in H26.
    pose proof Z.max_lub_l _ _ _ H26.
    pose proof Z.max_lub_r _ _ _ H26.
    (* Search (Z.max _ _ <= _). *)
    rewrite H_c1, H_c2, H_c3.
    unfold prop_cnt_inf.
    apply Z.max_lub.
    + simpl.
      repeat apply Z.max_lub; try lia.
    + simpl.
      (* Search (Z.abs _ <= _). *)
      apply Z.abs_le.
      split.
      - (*Search (_ <= Z.min _ _). *)
        repeat apply Z.min_glb; try lia.
      - (*Search (Z.min _ _ <= _). *)
        pose proof Z.le_min_l (Z.min p1_pre (Z.min (- p3_pre) (Z.min 0 0)))
        (Z.min (Z.min p2_pre (Z.min (- p3_pre) (Z.min 0 0)))
           (Z.min (Z.min (- p1_pre) (Z.min (- p2_pre) (Z.min p3_pre 0))) (min_cnf clist))).
        pose proof Z.le_min_l p1_pre (Z.min (- p3_pre) (Z.min 0 0)).
        remember (Z.min (Z.min p1_pre (Z.min (- p3_pre) (Z.min 0 0)))
        (Z.min (Z.min p2_pre (Z.min (- p3_pre) (Z.min 0 0)))
           (Z.min (Z.min (- p1_pre) (Z.min (- p2_pre) (Z.min p3_pre 0))) (min_cnf clist)))) as tmp2 eqn:H2000.
        remember (Z.min p1_pre (Z.min (- p3_pre) (Z.min 0 0))) as tmp1 eqn:H1000.
        clear H1000 H2000.
        lia.
  }
  clear - H2 H31.
  entailer!.
Qed.

Lemma proof_of_clause_gen_binary_return_wit_1_6 : clause_gen_binary_return_wit_1_6.
Proof.
  pre_process.
  clear H24 H25.
  rename H26 into H24.
  rewrite all_zero_list_3.
  repeat rewrite replace_0th.
  repeat rewrite replace_1st.
  repeat rewrite replace_2nd.
  assert (bop = SMTPROP_IMPLY). {
    destruct bop; unfold SmtPBID in *; try contradiction; try lia.
    reflexivity.
  }
  clear H23 H24.
  remember (- p1_pre :: p2_pre :: - p3_pre :: nil) as c1 eqn:H_c1.
  remember (- p2_pre :: p3_pre :: 0 :: nil) as c2 eqn:H_c2.
  remember (p1_pre :: p3_pre :: 0 :: nil) as c3 eqn:H_c3.
  pose proof store_cnf_list_fold.
  sep_apply (H23 retval_7 c1 retval_3); try easy.
  sep_apply (H23 retval_6 c2 retval_2); try easy.
  sep_apply (H23 retval_5 c3 retval); try easy.
  clear H23.
  pose proof @sllseg_len1 cnf_list_cell store_cnf_list_cell "cnf_list" "next".
  sep_apply (H23 retval_5 c3 retval_6); try easy.
  sep_apply (H23 retval_6 c2 retval_7); try easy.
  sep_apply (H23 retval_7 c1 y); try easy.
  clear H23.
  pose proof @sllseg_sll cnf_list_cell store_cnf_list_cell "cnf_list" "next".
  unfold sll_cnf_list.
  sep_apply (H23 retval_7 y (c1 :: nil) clist); try easy.
  sep_apply (H23 retval_6 retval_7 (c2 :: nil) ((c1 :: nil) ++ clist)); try easy.
  sep_apply (H23 retval_5 retval_6 (c3 :: nil) ((c2 :: nil) ++ (c1 :: nil) ++ clist)); try easy.
  clear H23.
  unfold store_predata.
  Exists retval_5.
  rewrite H25.
  unfold iff2cnf_length_binary, iff2cnf_binary.
  destruct (p1_pre ==? p2_pre); try contradiction.
  repeat rewrite <- app_comm_cons.
  unfold app.
  rewrite <- H_c1, <- H_c2, <- H_c3.
  assert (Zlength (c3 :: c2 :: c1 :: clist) = ccnt + 3). {
    repeat rewrite Zlength_cons.
    rewrite H3.
    lia.
  }
  rewrite H23.
  assert (prop_cnt_inf (c3 :: c2 :: c1 :: clist) <= pcnt). {
    pose proof prop_cnt_nneg clist.
    clear H24 H26 H27 H28 H29 H30.
    assert (pcnt >= 1) by lia.
    assert (prop_cnt_inf clist <= pcnt - 1) by lia.
    unfold prop_cnt_inf in H26.
    pose proof Z.max_lub_l _ _ _ H26.
    pose proof Z.max_lub_r _ _ _ H26.
    (* Search (Z.max _ _ <= _). *)
    rewrite H_c1, H_c2, H_c3.
    unfold prop_cnt_inf.
    apply Z.max_lub.
    + simpl.
      repeat apply Z.max_lub; try lia.
    + simpl.
      (* Search (Z.abs _ <= _). *)
      apply Z.abs_le.
      split.
      - (*Search (_ <= Z.min _ _). *)
        repeat apply Z.min_glb; try lia.
      - (*Search (Z.min _ _ <= _). *)
        pose proof Z.le_min_l (Z.min p1_pre (Z.min p3_pre (Z.min 0 0)))
        (Z.min (Z.min (- p2_pre) (Z.min p3_pre (Z.min 0 0)))
           (Z.min (Z.min (- p1_pre) (Z.min p2_pre (Z.min (- p3_pre) 0))) (min_cnf clist))).
        pose proof Z.le_min_l p1_pre (Z.min p3_pre (Z.min 0 0)).
        remember (Z.min (Z.min p1_pre (Z.min p3_pre (Z.min 0 0)))
        (Z.min (Z.min (- p2_pre) (Z.min p3_pre (Z.min 0 0)))
           (Z.min (Z.min (- p1_pre) (Z.min p2_pre (Z.min (- p3_pre) 0))) (min_cnf clist)))) as tmp2 eqn:H2000.
        remember (Z.min p1_pre (Z.min p3_pre (Z.min 0 0))) as tmp1 eqn:H1000.
        clear H1000 H2000.
        lia.
  }
  clear - H2 H31.
  entailer!.
Qed.

Lemma proof_of_clause_gen_binary_return_wit_1_7 : clause_gen_binary_return_wit_1_7.
Proof.
  pre_process.
  (* clear H24 H25.
  rename H26 into H24. *)
  rewrite all_zero_list_3.
  repeat rewrite replace_0th.
  repeat rewrite replace_1st.
  repeat rewrite replace_2nd.
  assert (bop = SMTPROP_IMPLY). {
    destruct bop; unfold SmtPBID in *; try contradiction; try lia.
    reflexivity.
  }
  clear H23 H24.
  remember (p3_pre :: 0 :: 0 :: nil) as c1 eqn:H_c1.
  pose proof store_cnf_list_fold.
  sep_apply (H23 retval_5 c1 retval); try easy.
  clear H23.
  pose proof @sllseg_len1 cnf_list_cell store_cnf_list_cell "cnf_list" "next".
  sep_apply (H23 retval_5 c1 y); try easy.
  clear H23.
  pose proof @sllseg_sll cnf_list_cell store_cnf_list_cell "cnf_list" "next".
  unfold sll_cnf_list.
  sep_apply (H23 retval_5 y (c1 :: nil) clist); try easy.
  clear H23.
  unfold store_predata.
  Exists retval_5.
  rewrite H25.
  unfold iff2cnf_length_binary, iff2cnf_binary.
  destruct (p1_pre ==? p2_pre); try contradiction.
  repeat rewrite <- app_comm_cons.
  unfold app.
  rewrite <- H_c1.
  assert (Zlength (c1 :: clist) = ccnt + 1). {
    repeat rewrite Zlength_cons.
    rewrite H1.
    lia.
  }
  rewrite H23.
  assert (prop_cnt_inf (c1 :: clist) <= pcnt). {
    pose proof prop_cnt_nneg clist.
    clear H24 H26.
    assert (pcnt >= 1) by lia.
    assert (prop_cnt_inf clist <= pcnt - 1) by lia.
    unfold prop_cnt_inf in H26.
    pose proof Z.max_lub_l _ _ _ H26.
    pose proof Z.max_lub_r _ _ _ H26.
    (* Search (Z.max _ _ <= _). *)
    rewrite H_c1.
    unfold prop_cnt_inf.
    apply Z.max_lub.
    + simpl.
      repeat apply Z.max_lub; try lia.
    + simpl.
      (* Search (Z.abs _ <= _). *)
      apply Z.abs_le.
      split.
      - (*Search (_ <= Z.min _ _). *)
        repeat apply Z.min_glb; try lia.
      - (*Search (Z.min _ _ <= _). *)
        pose proof Z.le_min_r (Z.min p3_pre (Z.min 0 (Z.min 0 0))) (min_cnf clist).
        remember (Z.min (Z.min p3_pre (Z.min 0 (Z.min 0 0))) (min_cnf clist)) as tmp1 eqn:H1000.
        clear H1000.
        lia.
  }
  clear - H0 H27.
  entailer!.
Qed.

Lemma proof_of_clause_gen_binary_return_wit_1_8 : clause_gen_binary_return_wit_1_8.
Proof.
  pre_process.
  clear H24.
  rename H25 into H24.
  rewrite all_zero_list_3.
  repeat rewrite replace_0th.
  repeat rewrite replace_1st.
  repeat rewrite replace_2nd.
  assert (bop = SMTPROP_IFF). {
    destruct bop; unfold SmtPBID in *; try contradiction; try lia.
    reflexivity.
  }
  clear H23 H24.
  remember (p3_pre :: 0 :: 0 :: nil) as c1 eqn:H_c1.
  pose proof store_cnf_list_fold.
  sep_apply (H23 retval_5 c1 retval); try easy.
  clear H23.
  pose proof @sllseg_len1 cnf_list_cell store_cnf_list_cell "cnf_list" "next".
  sep_apply (H23 retval_5 c1 y); try easy.
  clear H23.
  pose proof @sllseg_sll cnf_list_cell store_cnf_list_cell "cnf_list" "next".
  unfold sll_cnf_list.
  sep_apply (H23 retval_5 y (c1 :: nil) clist); try easy.
  clear H23.
  unfold store_predata.
  Exists retval_5.
  rewrite H25.
  unfold iff2cnf_length_binary, iff2cnf_binary.
  destruct (p1_pre ==? p2_pre); try contradiction.
  repeat rewrite <- app_comm_cons.
  unfold app.
  rewrite <- H_c1.
  assert (Zlength (c1 :: clist) = ccnt + 1). {
    repeat rewrite Zlength_cons.
    rewrite H1.
    lia.
  }
  rewrite H23.
  assert (prop_cnt_inf (c1 :: clist) <= pcnt). {
    pose proof prop_cnt_nneg clist.
    clear H24 H26.
    assert (pcnt >= 1) by lia.
    assert (prop_cnt_inf clist <= pcnt - 1) by lia.
    unfold prop_cnt_inf in H26.
    pose proof Z.max_lub_l _ _ _ H26.
    pose proof Z.max_lub_r _ _ _ H26.
    (* Search (Z.max _ _ <= _). *)
    rewrite H_c1.
    unfold prop_cnt_inf.
    apply Z.max_lub.
    + simpl.
      repeat apply Z.max_lub; try lia.
    + simpl.
      (* Search (Z.abs _ <= _). *)
      apply Z.abs_le.
      split.
      - (*Search (_ <= Z.min _ _). *)
        repeat apply Z.min_glb; try lia.
      - (*Search (Z.min _ _ <= _). *)
        pose proof Z.le_min_r (Z.min p3_pre (Z.min 0 (Z.min 0 0))) (min_cnf clist).
        remember (Z.min (Z.min p3_pre (Z.min 0 (Z.min 0 0))) (min_cnf clist)) as tmp1 eqn:H1000.
        clear H1000.
        lia.
  }
  clear - H0 H27.
  entailer!.
Qed.

Lemma proof_of_clause_gen_binary_which_implies_wit_1 : clause_gen_binary_which_implies_wit_1.
Proof.
  pre_process.
  unfold store_predata.
  Intros y.
  Exists y.
  entailer!.
Qed. 

Lemma proof_of_prop2cnf_safety_wit_3 : prop2cnf_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_prop2cnf_safety_wit_6 : prop2cnf_safety_wit_6.
Proof. Admitted. 

Lemma proof_of_prop2cnf_safety_wit_9 : prop2cnf_safety_wit_9.
Proof. Admitted. 

Lemma proof_of_prop2cnf_return_wit_1_1 : prop2cnf_return_wit_1_1.
Proof.
  pre_process.
  clear H4 H5.
  rename H6 into H4.
  Exists clist pcnt ccnt var.
  unfold store_predata.
  Intros y.
  Exists y.
  entailer!; rewrite H in *.
  + unfold SmtPTID, store_SmtProp.
    unfold SmtPTID.
    entailer!.
  + rewrite prop_cnt_inf_var in *.
    lia.
  + rewrite prop_cnt_inf_var in *.
    lia.
  + unfold make_predata, make_prop2cnf_ret.
    unfold prop2cnf_logic.
    reflexivity.
Qed.

Lemma proof_of_prop2cnf_return_wit_1_2 : prop2cnf_return_wit_1_2.
Proof.
  pre_process.
  clear H15.
  rewrite H11 in *.
  unfold SmtPTID in *.
  clear H16.
  unfold store_predata.
  Intros y0.
  unfold iff2cnf_unary.
  repeat rewrite <- app_comm_cons.
  unfold app.
  remember (retval :: pcnt'' + 1 :: 0 :: nil) as c1 eqn:H_c1.
  remember (- retval :: - (pcnt'' + 1) :: 0 :: nil) as c2 eqn:H_c2.
  Exists (c1 :: c2 :: clist'') (pcnt'' + 1) (ccnt'' + 2) (pcnt'' + 1) y0.
  entailer!.
  1: {
    simpl store_SmtProp.
    Exists y.
    entailer!.
  }
  2: {
    unfold make_prop2cnf_ret, make_predata.
    simpl.
    remember (prop2cnf_logic (SmtU op sub_prop) (clist, pcnt, ccnt)) as step1 eqn:Hstep1.
    destruct step1 as [data1 p1].
    
    remember (prop2cnf_logic sub_prop (clist, pcnt, ccnt)) as step2 eqn:Hstep2.
    destruct step2 as [data2 p2].
    
    destruct data2 as [tmp clause_cnt].
    destruct tmp as [cnf_res prop_cnt].
    unfold make_prop2cnf_ret, make_predata in H5.
    rewrite <- H5 in Hstep2.
    inversion Hstep2.
    subst.
    rewrite <- H_c1, H_c2.
    inversion.
  }
  + unfold make_prop2cnf_ret, make_predata in H5.
Qed.

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

