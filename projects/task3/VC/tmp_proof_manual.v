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
Require Import tmp_goal.
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

Lemma proof_of_sub_thm_return_wit_1 : sub_thm_return_wit_1.
Proof.
  pre_process.
  rewrite H.
  unfold sll_var_sub_list.
  pose proof (sll_zero store_var_sub_cell "var_sub_list"
  "next" 0 l).
  unfold NULL in H0.
  assert (0 = 0).
  lia.
  pose proof (H0 H1); clear H0 H1.
  destruct l.
  unfold thm_subst.
  entailer!.
  (* replace (eqb v :: l nil) with False in H2.
  sep_apply H2.
  entailer!. *)
Admitted.

Lemma proof_of_sub_thm_return_wit_2 : sub_thm_return_wit_2.
Proof.
  pre_process.
  rewrite H2.
Admitted.

Lemma proof_of_sub_thm_return_wit_3 : sub_thm_return_wit_3.
Proof.
  pre_process.
  unfold store_term_res.
  (* unfold sll_var_sub_list at 2. unfold sll.
  destruct (thm_subst t l) eqn:E.
  unfold store_term. *)
Admitted.

Lemma proof_of_sub_thm_partial_solve_wit_3_pure : sub_thm_partial_solve_wit_3_pure.
Proof.
  pre_process.
  sep_apply store_term_unfold.
  sep_apply store_term_unfold.
  unfold store_string, NULL.
  Intros n1 n2.
  entailer!.
Qed.

Lemma proof_of_sub_thm_which_implies_wit_1 : sub_thm_which_implies_wit_1.
Proof.
  pre_process.
Admitted.

Lemma proof_of_sub_thm_which_implies_wit_2 : sub_thm_which_implies_wit_2.
Proof.
  pre_process.
Admitted. 

Lemma proof_of_check_list_gen_entail_wit_2 : check_list_gen_entail_wit_2.
Proof. Admitted. 

Lemma proof_of_check_list_gen_return_wit_1 : check_list_gen_return_wit_1.
Proof. Admitted. 

Lemma proof_of_check_list_gen_return_wit_2_1 : check_list_gen_return_wit_2_1.
Proof. Admitted. 

Lemma proof_of_check_list_gen_return_wit_2_2 : check_list_gen_return_wit_2_2.
Proof. Admitted. 

Lemma proof_of_check_list_gen_return_wit_3 : check_list_gen_return_wit_3.
Proof. Admitted. 

Lemma proof_of_check_list_gen_which_implies_wit_1 : check_list_gen_which_implies_wit_1.
Proof. Admitted. 

Lemma proof_of_check_list_gen_which_implies_wit_2 : check_list_gen_which_implies_wit_2.
Proof. Admitted. 

Lemma proof_of_check_list_gen_which_implies_wit_3 : check_list_gen_which_implies_wit_3.
Proof. Admitted. 

Lemma proof_of_thm_apply_return_wit_1_1 : thm_apply_return_wit_1_1.
Proof.
  pre_process.
  unfold store_solve_res.
  assert ((thm_app t l g) = SRTList (gen_pre tst g)) .
  2:{
    rewrite H6.
    unfold restypeID.
    Exists retval_2.
    entailer!.
    admit.
  }
Admitted.

Lemma proof_of_thm_apply_return_wit_1_2 : thm_apply_return_wit_1_2.
Proof.
  pre_process.
Admitted.

Lemma proof_of_thm_apply_return_wit_1_3 : thm_apply_return_wit_1_3.
Proof.
  pre_process.
  entailer!.
Admitted.

Lemma proof_of_thm_apply_which_implies_wit_1 : thm_apply_which_implies_wit_1.
Proof.
  pre_process.
  Exists 0 0.
  unfold store_solve_res.
  unfold restypeID, NULL.
  entailer!.
Qed.

Lemma proof_of_thm_apply_which_implies_wit_2 : thm_apply_which_implies_wit_2.
Proof.
  pre_process.
  unfold store_term_res.
  destruct (thm_subst t l) eqn:E.
  - Exists t0.
    entailer!.
  - entailer!.
Qed. 

Lemma proof_of_thm_apply_which_implies_wit_3 : thm_apply_which_implies_wit_3.
Proof.
  pre_process.
  rewrite H.
  Exists 0.
  entailer!.
Admitted.
