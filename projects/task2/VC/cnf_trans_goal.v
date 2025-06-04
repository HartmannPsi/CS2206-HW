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

(*----- Function clause_gen_unary -----*)

Definition clause_gen_unary_safety_wit_1 := 
forall (data_pre: Z) (p3_pre: Z) (p2_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) ,
  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |]
  &&  ((( &( "size" ) )) # Int  |->_)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition clause_gen_unary_safety_wit_2 := 
forall (data_pre: Z) (p3_pre: Z) (p2_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval_2: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |]
  &&  (store_int_array retval 3 (all_zero_list (3)) )
  **  ((( &( "clause2" ) )) # Ptr  |-> retval)
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  ((( &( "clause1" ) )) # Ptr  |-> retval_2)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition clause_gen_unary_safety_wit_3 := 
forall (data_pre: Z) (p3_pre: Z) (p2_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |]
  &&  (store_int_array retval 3 (replace_Znth (0) (p2_pre) ((all_zero_list (3)))) )
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition clause_gen_unary_safety_wit_4 := 
forall (data_pre: Z) (p3_pre: Z) (p2_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |]
  &&  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition clause_gen_unary_safety_wit_5 := 
forall (data_pre: Z) (p3_pre: Z) (p2_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |]
  &&  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p2_pre <> (INT_MIN)) |]
.

Definition clause_gen_unary_safety_wit_6 := 
forall (data_pre: Z) (p3_pre: Z) (p2_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |]
  &&  (store_int_array retval_2 3 (replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition clause_gen_unary_safety_wit_7 := 
forall (data_pre: Z) (p3_pre: Z) (p2_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |]
  &&  (store_int_array retval_2 3 (replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p3_pre <> (INT_MIN)) |]
.

Definition clause_gen_unary_safety_wit_8 := 
forall (data_pre: Z) (p3_pre: Z) (p2_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (y: Z) ,
  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_3)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
  **  ((&((retval_4)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_4)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_4)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_4)
  **  ((&((retval_3)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_3)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_3)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_4)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_3)
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
|--
  [| ((ccnt + 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (ccnt + 2 )) |]
.

Definition clause_gen_unary_safety_wit_9 := 
forall (data_pre: Z) (p3_pre: Z) (p2_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (y: Z) ,
  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_3)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
  **  ((&((retval_4)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_4)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_4)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_4)
  **  ((&((retval_3)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_3)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_3)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_4)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_3)
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition clause_gen_unary_return_wit_1 := 
forall (data_pre: Z) (p3_pre: Z) (p2_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (y: Z) ,
  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_3)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 2 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_4)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_4)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_4)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((retval_3)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_3)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_3)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_4)
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
|--
  (store_predata data_pre (app ((iff2cnf_unary (p2_pre) (p3_pre))) (clist)) pcnt (ccnt + 2 ) )
.

Definition clause_gen_unary_partial_solve_wit_1_pure := 
forall (data_pre: Z) (p3_pre: Z) (p2_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) ,
  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |]
  &&  ((( &( "clause1" ) )) # Ptr  |->_)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (3 > 0) |]
.

Definition clause_gen_unary_partial_solve_wit_1_aux := 
forall (data_pre: Z) (p3_pre: Z) (p2_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) ,
  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |]
  &&  (store_predata data_pre clist pcnt ccnt )
|--
  [| (3 > 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |]
  &&  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_unary_partial_solve_wit_1 := clause_gen_unary_partial_solve_wit_1_pure -> clause_gen_unary_partial_solve_wit_1_aux.

Definition clause_gen_unary_partial_solve_wit_2_pure := 
forall (data_pre: Z) (p3_pre: Z) (p2_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |]
  &&  ((( &( "clause2" ) )) # Ptr  |->_)
  **  (store_int_array retval 3 (all_zero_list (3)) )
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (3 > 0) |]
.

Definition clause_gen_unary_partial_solve_wit_2_aux := 
forall (data_pre: Z) (p3_pre: Z) (p2_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |]
  &&  (store_int_array retval 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (3 > 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |]
  &&  (store_int_array retval 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_unary_partial_solve_wit_2 := clause_gen_unary_partial_solve_wit_2_pure -> clause_gen_unary_partial_solve_wit_2_aux.

Definition clause_gen_unary_partial_solve_wit_3 := 
forall (data_pre: Z) (p3_pre: Z) (p2_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |]
  &&  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  (store_int_array retval 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |]
  &&  (((retval + (0 * sizeof(INT) ) )) # Int  |->_)
  **  (store_int_array_missing_i_rec retval 0 0 3 (all_zero_list (3)) )
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_unary_partial_solve_wit_4 := 
forall (data_pre: Z) (p3_pre: Z) (p2_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |]
  &&  (store_int_array retval 3 (replace_Znth (0) (p2_pre) ((all_zero_list (3)))) )
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |]
  &&  (((retval + (1 * sizeof(INT) ) )) # Int  |->_)
  **  (store_int_array_missing_i_rec retval 1 0 3 (replace_Znth (0) (p2_pre) ((all_zero_list (3)))) )
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_unary_partial_solve_wit_5 := 
forall (data_pre: Z) (p3_pre: Z) (p2_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |]
  &&  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |]
  &&  (((retval_2 + (0 * sizeof(INT) ) )) # Int  |->_)
  **  (store_int_array_missing_i_rec retval_2 0 0 3 (all_zero_list (3)) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_unary_partial_solve_wit_6 := 
forall (data_pre: Z) (p3_pre: Z) (p2_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |]
  &&  (store_int_array retval_2 3 (replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |]
  &&  (((retval_2 + (1 * sizeof(INT) ) )) # Int  |->_)
  **  (store_int_array_missing_i_rec retval_2 1 0 3 (replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_unary_partial_solve_wit_7 := 
forall (data_pre: Z) (p3_pre: Z) (p2_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |]
  &&  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |]
  &&  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_unary_partial_solve_wit_8 := 
forall (data_pre: Z) (p3_pre: Z) (p2_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) ,
  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |]
  &&  ((&((retval_3)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_3)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_3)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |]
  &&  ((&((retval_3)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_3)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_3)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_unary_partial_solve_wit_9 := 
forall (data_pre: Z) (p3_pre: Z) (p2_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |]
  &&  ((&((retval_4)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_4)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_4)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_3)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_3)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_3)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_4)
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |]
  &&  (store_predata data_pre clist pcnt ccnt )
  **  ((&((retval_4)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_4)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_4)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_3)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_3)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_3)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_4)
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
.

Definition clause_gen_unary_which_implies_wit_1 := 
forall (data_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) ,
  (store_predata data_pre clist pcnt ccnt )
|--
  EX (y: Z) ,
  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
.

(*----- Function clause_gen_binary -----*)

Definition clause_gen_binary_safety_wit_1 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) ,
  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |]
  &&  ((( &( "size" ) )) # Int  |->_)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition clause_gen_binary_safety_wit_2 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |]
  &&  ((( &( "cnt" ) )) # Int  |->_)
  **  (store_int_array retval 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_4)
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_3)
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  ((( &( "clause1" ) )) # Ptr  |-> retval_2)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition clause_gen_binary_safety_wit_3 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |]
  &&  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_4)
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_3)
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  ((( &( "clause1" ) )) # Ptr  |-> retval_2)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition clause_gen_binary_safety_wit_4 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_4)
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_3)
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  ((( &( "clause1" ) )) # Ptr  |-> retval_2)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition clause_gen_binary_safety_wit_5 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_4)
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_3)
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  ((( &( "clause1" ) )) # Ptr  |-> retval_2)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p1_pre <> (INT_MIN)) |]
.

Definition clause_gen_binary_safety_wit_6 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  (store_int_array retval 3 (replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition clause_gen_binary_safety_wit_7 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition clause_gen_binary_safety_wit_8 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p2_pre <> (INT_MIN)) |]
.

Definition clause_gen_binary_safety_wit_9 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  (store_int_array retval_2 3 (replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition clause_gen_binary_safety_wit_10 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition clause_gen_binary_safety_wit_11 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  (store_int_array retval_3 3 (replace_Znth (0) (p1_pre) ((all_zero_list (3)))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition clause_gen_binary_safety_wit_12 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  (store_int_array retval_3 3 (replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition clause_gen_binary_safety_wit_13 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  (store_int_array retval_3 3 (replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p3_pre <> (INT_MIN)) |]
.

Definition clause_gen_binary_safety_wit_14 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition clause_gen_binary_safety_wit_15 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  (store_int_array retval_3 3 (replace_Znth (0) (p1_pre) ((all_zero_list (3)))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition clause_gen_binary_safety_wit_16 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  (store_int_array retval_3 3 (replace_Znth (0) (p1_pre) ((all_zero_list (3)))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p3_pre <> (INT_MIN)) |]
.

Definition clause_gen_binary_safety_wit_17 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| ((0 + 3 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (0 + 3 )) |]
.

Definition clause_gen_binary_safety_wit_18 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition clause_gen_binary_safety_wit_19 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  (store_int_array retval_3 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| ((0 + 3 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (0 + 3 )) |]
.

Definition clause_gen_binary_safety_wit_20 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  (store_int_array retval_3 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition clause_gen_binary_safety_wit_21 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |]
  &&  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_4)
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_3)
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  ((( &( "clause1" ) )) # Ptr  |-> retval_2)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition clause_gen_binary_safety_wit_22 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_4)
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_3)
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  ((( &( "clause1" ) )) # Ptr  |-> retval_2)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition clause_gen_binary_safety_wit_23 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  (store_int_array retval 3 (replace_Znth (0) (p1_pre) ((all_zero_list (3)))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition clause_gen_binary_safety_wit_24 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  (store_int_array retval 3 (replace_Znth (0) (p1_pre) ((all_zero_list (3)))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p3_pre <> (INT_MIN)) |]
.

Definition clause_gen_binary_safety_wit_25 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition clause_gen_binary_safety_wit_26 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  (store_int_array retval_2 3 (replace_Znth (0) (p2_pre) ((all_zero_list (3)))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition clause_gen_binary_safety_wit_27 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  (store_int_array retval_2 3 (replace_Znth (0) (p2_pre) ((all_zero_list (3)))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p3_pre <> (INT_MIN)) |]
.

Definition clause_gen_binary_safety_wit_28 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition clause_gen_binary_safety_wit_29 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p1_pre <> (INT_MIN)) |]
.

Definition clause_gen_binary_safety_wit_30 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  (store_int_array retval_3 3 (replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition clause_gen_binary_safety_wit_31 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  (store_int_array retval_3 3 (replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p2_pre <> (INT_MIN)) |]
.

Definition clause_gen_binary_safety_wit_32 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  (store_int_array retval_3 3 (replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition clause_gen_binary_safety_wit_33 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition clause_gen_binary_safety_wit_34 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p1_pre <> (INT_MIN)) |]
.

Definition clause_gen_binary_safety_wit_35 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  (store_int_array retval_3 3 (replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition clause_gen_binary_safety_wit_36 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  (store_int_array retval_3 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| ((0 + 3 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (0 + 3 )) |]
.

Definition clause_gen_binary_safety_wit_37 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  (store_int_array retval_3 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition clause_gen_binary_safety_wit_38 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  (store_int_array retval_3 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| ((0 + 3 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (0 + 3 )) |]
.

Definition clause_gen_binary_safety_wit_39 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  (store_int_array retval_3 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition clause_gen_binary_safety_wit_40 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |]
  &&  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_4)
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_3)
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  ((( &( "clause1" ) )) # Ptr  |-> retval_2)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition clause_gen_binary_safety_wit_41 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_4)
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_3)
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  ((( &( "clause1" ) )) # Ptr  |-> retval_2)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition clause_gen_binary_safety_wit_42 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  (store_int_array retval 3 (replace_Znth (0) (p1_pre) ((all_zero_list (3)))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition clause_gen_binary_safety_wit_43 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition clause_gen_binary_safety_wit_44 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p2_pre <> (INT_MIN)) |]
.

Definition clause_gen_binary_safety_wit_45 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  (store_int_array retval_2 3 (replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition clause_gen_binary_safety_wit_46 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition clause_gen_binary_safety_wit_47 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p1_pre <> (INT_MIN)) |]
.

Definition clause_gen_binary_safety_wit_48 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  (store_int_array retval_3 3 (replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition clause_gen_binary_safety_wit_49 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  (store_int_array retval_3 3 (replace_Znth (1) (p2_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition clause_gen_binary_safety_wit_50 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  (store_int_array retval_3 3 (replace_Znth (1) (p2_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p3_pre <> (INT_MIN)) |]
.

Definition clause_gen_binary_safety_wit_51 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| ((0 + 3 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (0 + 3 )) |]
.

Definition clause_gen_binary_safety_wit_52 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition clause_gen_binary_safety_wit_53 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval: Z) ,
  [| (p1_pre = p2_pre) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_4)
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_3)
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  ((( &( "clause1" ) )) # Ptr  |-> retval_2)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition clause_gen_binary_safety_wit_54 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  (store_int_array retval 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| ((0 + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (0 + 1 )) |]
.

Definition clause_gen_binary_safety_wit_55 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  (store_int_array retval 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition clause_gen_binary_safety_wit_56 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |]
  &&  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_4)
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_3)
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  ((( &( "clause1" ) )) # Ptr  |-> retval_2)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition clause_gen_binary_safety_wit_57 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_4)
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_3)
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  ((( &( "clause1" ) )) # Ptr  |-> retval_2)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition clause_gen_binary_safety_wit_58 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  (store_int_array retval 3 (replace_Znth (0) (p1_pre) ((all_zero_list (3)))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition clause_gen_binary_safety_wit_59 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  (store_int_array retval 3 (replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition clause_gen_binary_safety_wit_60 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  (store_int_array retval 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition clause_gen_binary_safety_wit_61 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  (store_int_array retval 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p1_pre <> (INT_MIN)) |]
.

Definition clause_gen_binary_safety_wit_62 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  (store_int_array retval_2 3 (replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))) )
  **  (store_int_array retval 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition clause_gen_binary_safety_wit_63 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  (store_int_array retval_2 3 (replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))) )
  **  (store_int_array retval 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p2_pre <> (INT_MIN)) |]
.

Definition clause_gen_binary_safety_wit_64 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  (store_int_array retval_2 3 (replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition clause_gen_binary_safety_wit_65 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  (store_int_array retval_2 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition clause_gen_binary_safety_wit_66 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  (store_int_array retval_3 3 (replace_Znth (0) (p1_pre) ((all_zero_list (3)))) )
  **  (store_int_array retval_2 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition clause_gen_binary_safety_wit_67 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  (store_int_array retval_3 3 (replace_Znth (0) (p1_pre) ((all_zero_list (3)))) )
  **  (store_int_array retval_2 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p2_pre <> (INT_MIN)) |]
.

Definition clause_gen_binary_safety_wit_68 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  (store_int_array retval_3 3 (replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition clause_gen_binary_safety_wit_69 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  (store_int_array retval_3 3 (replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p3_pre <> (INT_MIN)) |]
.

Definition clause_gen_binary_safety_wit_70 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition clause_gen_binary_safety_wit_71 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p1_pre <> (INT_MIN)) |]
.

Definition clause_gen_binary_safety_wit_72 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  (store_int_array retval_4 3 (replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))) )
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition clause_gen_binary_safety_wit_73 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  (store_int_array retval_4 3 (replace_Znth (1) (p2_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition clause_gen_binary_safety_wit_74 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  (store_int_array retval_4 3 (replace_Znth (1) (p2_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p3_pre <> (INT_MIN)) |]
.

Definition clause_gen_binary_safety_wit_75 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  (store_int_array retval_4 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| ((0 + 4 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (0 + 4 )) |]
.

Definition clause_gen_binary_safety_wit_76 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  (store_int_array retval_4 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (4 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 4) |]
.

Definition clause_gen_binary_safety_wit_77 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval: Z) ,
  [| (p1_pre = p2_pre) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_4)
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_3)
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  ((( &( "clause1" ) )) # Ptr  |-> retval_2)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition clause_gen_binary_safety_wit_78 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  (store_int_array retval 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| ((0 + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (0 + 1 )) |]
.

Definition clause_gen_binary_safety_wit_79 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  (store_int_array retval 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition clause_gen_binary_safety_wit_80 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre <> 3) |]
  &&  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (store_int_array retval 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval)
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_4)
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_3)
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  ((( &( "clause1" ) )) # Ptr  |-> retval_2)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| False |]
.

Definition clause_gen_binary_safety_wit_81 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_3 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 3 ))
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition clause_gen_binary_safety_wit_82 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 3 ) = 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_3 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 3 ))
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| False |]
.

Definition clause_gen_binary_safety_wit_83 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 3 ))
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition clause_gen_binary_safety_wit_84 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 3 ) = 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 3 ))
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| False |]
.

Definition clause_gen_binary_safety_wit_85 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_3 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 3 ))
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition clause_gen_binary_safety_wit_86 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 3 ) = 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_3 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 3 ))
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| False |]
.

Definition clause_gen_binary_safety_wit_87 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_3 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 3 ))
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition clause_gen_binary_safety_wit_88 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 3 ) = 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_3 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 3 ))
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| False |]
.

Definition clause_gen_binary_safety_wit_89 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 3 ))
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition clause_gen_binary_safety_wit_90 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 3 ) = 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 3 ))
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| False |]
.

Definition clause_gen_binary_safety_wit_91 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 1 ))
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition clause_gen_binary_safety_wit_92 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 1 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 1 ))
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| False |]
.

Definition clause_gen_binary_safety_wit_93 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_4 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 4 ))
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition clause_gen_binary_safety_wit_94 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 4 ) = 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_4 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 4 ))
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| False |]
.

Definition clause_gen_binary_safety_wit_95 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 1 ))
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition clause_gen_binary_safety_wit_96 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 1 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 1 ))
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| False |]
.

Definition clause_gen_binary_safety_wit_97 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 1 ) = 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 1 ))
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| ((ccnt + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (ccnt + 1 )) |]
.

Definition clause_gen_binary_safety_wit_98 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 1 ) = 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 1 ))
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition clause_gen_binary_safety_wit_99 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 1 ) = 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 1 ))
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| ((ccnt + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (ccnt + 1 )) |]
.

Definition clause_gen_binary_safety_wit_100 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 1 ) = 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 1 ))
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition clause_gen_binary_safety_wit_101 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_3 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 3 ))
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition clause_gen_binary_safety_wit_102 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 3 ) = 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_3 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 3 ))
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| False |]
.

Definition clause_gen_binary_safety_wit_103 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 3 ))
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition clause_gen_binary_safety_wit_104 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 3 ) = 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 3 ))
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| False |]
.

Definition clause_gen_binary_safety_wit_105 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_3 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 3 ))
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition clause_gen_binary_safety_wit_106 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 3 ) = 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_3 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 3 ))
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| False |]
.

Definition clause_gen_binary_safety_wit_107 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_3 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 3 ))
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition clause_gen_binary_safety_wit_108 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 3 ) = 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_3 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 3 ))
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| False |]
.

Definition clause_gen_binary_safety_wit_109 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 3 ))
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition clause_gen_binary_safety_wit_110 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 3 ) = 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 3 ))
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| False |]
.

Definition clause_gen_binary_safety_wit_111 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 4 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_4 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 4 ))
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition clause_gen_binary_safety_wit_112 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 4 ) = 2) |] 
  &&  [| ((0 + 4 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_4 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 4 ))
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| False |]
.

Definition clause_gen_binary_safety_wit_113 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 3 ) <> 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_3 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 3 ))
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition clause_gen_binary_safety_wit_114 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 3 ) <> 3) |] 
  &&  [| ((0 + 3 ) <> 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_3 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 3 ))
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| False |]
.

Definition clause_gen_binary_safety_wit_115 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 3 ) <> 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 3 ))
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition clause_gen_binary_safety_wit_116 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 3 ) <> 3) |] 
  &&  [| ((0 + 3 ) <> 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 3 ))
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| False |]
.

Definition clause_gen_binary_safety_wit_117 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 3 ) <> 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_3 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 3 ))
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition clause_gen_binary_safety_wit_118 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 3 ) <> 3) |] 
  &&  [| ((0 + 3 ) <> 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_3 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 3 ))
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| False |]
.

Definition clause_gen_binary_safety_wit_119 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 3 ) <> 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_3 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 3 ))
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition clause_gen_binary_safety_wit_120 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 3 ) <> 3) |] 
  &&  [| ((0 + 3 ) <> 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_3 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 3 ))
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| False |]
.

Definition clause_gen_binary_safety_wit_121 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 3 ) <> 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 3 ))
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition clause_gen_binary_safety_wit_122 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 3 ) <> 3) |] 
  &&  [| ((0 + 3 ) <> 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 3 ))
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| False |]
.

Definition clause_gen_binary_safety_wit_123 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 4 ) <> 2) |] 
  &&  [| ((0 + 4 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_4 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 4 ))
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition clause_gen_binary_safety_wit_124 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 4 ) = 3) |] 
  &&  [| ((0 + 4 ) <> 2) |] 
  &&  [| ((0 + 4 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_4 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 4 ))
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| False |]
.

Definition clause_gen_binary_safety_wit_125 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 3 ) = 3) |] 
  &&  [| ((0 + 3 ) <> 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_7)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_6)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_3 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 3 ))
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| ((ccnt + 3 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (ccnt + 3 )) |]
.

Definition clause_gen_binary_safety_wit_126 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 3 ) = 3) |] 
  &&  [| ((0 + 3 ) <> 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_7)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_6)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_3 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 3 ))
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition clause_gen_binary_safety_wit_127 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 3 ) = 3) |] 
  &&  [| ((0 + 3 ) <> 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_7)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_6)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 3 ))
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| ((ccnt + 3 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (ccnt + 3 )) |]
.

Definition clause_gen_binary_safety_wit_128 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 3 ) = 3) |] 
  &&  [| ((0 + 3 ) <> 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_7)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_6)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 3 ))
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition clause_gen_binary_safety_wit_129 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 3 ) = 3) |] 
  &&  [| ((0 + 3 ) <> 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_7)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_6)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_3 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 3 ))
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| ((ccnt + 3 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (ccnt + 3 )) |]
.

Definition clause_gen_binary_safety_wit_130 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 3 ) = 3) |] 
  &&  [| ((0 + 3 ) <> 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_7)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_6)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_3 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 3 ))
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition clause_gen_binary_safety_wit_131 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 3 ) = 3) |] 
  &&  [| ((0 + 3 ) <> 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_7)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_6)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_3 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 3 ))
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| ((ccnt + 3 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (ccnt + 3 )) |]
.

Definition clause_gen_binary_safety_wit_132 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 3 ) = 3) |] 
  &&  [| ((0 + 3 ) <> 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_7)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_6)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_3 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 3 ))
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition clause_gen_binary_safety_wit_133 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 3 ) = 3) |] 
  &&  [| ((0 + 3 ) <> 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_7)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_6)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 3 ))
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| ((ccnt + 3 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (ccnt + 3 )) |]
.

Definition clause_gen_binary_safety_wit_134 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 3 ) = 3) |] 
  &&  [| ((0 + 3 ) <> 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_7)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_6)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 3 ))
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition clause_gen_binary_safety_wit_135 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 4 ) <> 3) |] 
  &&  [| ((0 + 4 ) <> 2) |] 
  &&  [| ((0 + 4 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_8)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_7)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_6)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_4 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 4 ))
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| ((ccnt + 4 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (ccnt + 4 )) |]
.

Definition clause_gen_binary_safety_wit_136 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 4 ) <> 3) |] 
  &&  [| ((0 + 4 ) <> 2) |] 
  &&  [| ((0 + 4 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_8)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_7)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_6)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_4 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 4 ))
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_2)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| (4 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 4) |]
.

Definition clause_gen_binary_return_wit_1_1 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 4 ) <> 3) |] 
  &&  [| ((0 + 4 ) <> 2) |] 
  &&  [| ((0 + 4 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 4 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_8)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_7)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_6)
  **  (store_int_array retval_4 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
|--
  (store_predata data_pre (app ((iff2cnf_binary (p1_pre) (p2_pre) (p3_pre) (bop))) (clist)) pcnt (ccnt + (iff2cnf_length_binary (p1_pre) (p2_pre) (p3_pre) (bop)) ) )
.

Definition clause_gen_binary_return_wit_1_2 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 3 ) = 3) |] 
  &&  [| ((0 + 3 ) <> 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 3 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_7)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_6)
  **  (store_int_array retval_3 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
|--
  (store_predata data_pre (app ((iff2cnf_binary (p1_pre) (p2_pre) (p3_pre) (bop))) (clist)) pcnt (ccnt + (iff2cnf_length_binary (p1_pre) (p2_pre) (p3_pre) (bop)) ) )
.

Definition clause_gen_binary_return_wit_1_3 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 3 ) = 3) |] 
  &&  [| ((0 + 3 ) <> 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 3 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_7)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_6)
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
|--
  (store_predata data_pre (app ((iff2cnf_binary (p1_pre) (p2_pre) (p3_pre) (bop))) (clist)) pcnt (ccnt + (iff2cnf_length_binary (p1_pre) (p2_pre) (p3_pre) (bop)) ) )
.

Definition clause_gen_binary_return_wit_1_4 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 3 ) = 3) |] 
  &&  [| ((0 + 3 ) <> 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 3 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_7)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_6)
  **  (store_int_array retval_3 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
|--
  (store_predata data_pre (app ((iff2cnf_binary (p1_pre) (p2_pre) (p3_pre) (bop))) (clist)) pcnt (ccnt + (iff2cnf_length_binary (p1_pre) (p2_pre) (p3_pre) (bop)) ) )
.

Definition clause_gen_binary_return_wit_1_5 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 3 ) = 3) |] 
  &&  [| ((0 + 3 ) <> 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 3 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_7)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_6)
  **  (store_int_array retval_3 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
|--
  (store_predata data_pre (app ((iff2cnf_binary (p1_pre) (p2_pre) (p3_pre) (bop))) (clist)) pcnt (ccnt + (iff2cnf_length_binary (p1_pre) (p2_pre) (p3_pre) (bop)) ) )
.

Definition clause_gen_binary_return_wit_1_6 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 3 ) = 3) |] 
  &&  [| ((0 + 3 ) <> 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 3 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_7)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_6)
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
|--
  (store_predata data_pre (app ((iff2cnf_binary (p1_pre) (p2_pre) (p3_pre) (bop))) (clist)) pcnt (ccnt + (iff2cnf_length_binary (p1_pre) (p2_pre) (p3_pre) (bop)) ) )
.

Definition clause_gen_binary_return_wit_1_7 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 1 ) = 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 1 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  (store_int_array retval 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
|--
  (store_predata data_pre (app ((iff2cnf_binary (p1_pre) (p2_pre) (p3_pre) (bop))) (clist)) pcnt (ccnt + (iff2cnf_length_binary (p1_pre) (p2_pre) (p3_pre) (bop)) ) )
.

Definition clause_gen_binary_return_wit_1_8 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 1 ) = 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 1 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  (store_int_array retval 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
|--
  (store_predata data_pre (app ((iff2cnf_binary (p1_pre) (p2_pre) (p3_pre) (bop))) (clist)) pcnt (ccnt + (iff2cnf_length_binary (p1_pre) (p2_pre) (p3_pre) (bop)) ) )
.

Definition clause_gen_binary_partial_solve_wit_1_pure := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) ,
  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |]
  &&  ((( &( "clause1" ) )) # Ptr  |->_)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (3 > 0) |]
.

Definition clause_gen_binary_partial_solve_wit_1_aux := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) ,
  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |]
  &&  (store_predata data_pre clist pcnt ccnt )
|--
  [| (3 > 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |]
  &&  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_1 := clause_gen_binary_partial_solve_wit_1_pure -> clause_gen_binary_partial_solve_wit_1_aux.

Definition clause_gen_binary_partial_solve_wit_2_pure := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |]
  &&  ((( &( "clause2" ) )) # Ptr  |->_)
  **  (store_int_array retval 3 (all_zero_list (3)) )
  **  ((( &( "clause1" ) )) # Ptr  |-> retval)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (3 > 0) |]
.

Definition clause_gen_binary_partial_solve_wit_2_aux := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |]
  &&  (store_int_array retval 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (3 > 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |]
  &&  (store_int_array retval 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_2 := clause_gen_binary_partial_solve_wit_2_pure -> clause_gen_binary_partial_solve_wit_2_aux.

Definition clause_gen_binary_partial_solve_wit_3_pure := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval_2: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |]
  &&  ((( &( "clause3" ) )) # Ptr  |->_)
  **  (store_int_array retval 3 (all_zero_list (3)) )
  **  ((( &( "clause2" ) )) # Ptr  |-> retval)
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  ((( &( "clause1" ) )) # Ptr  |-> retval_2)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (3 > 0) |]
.

Definition clause_gen_binary_partial_solve_wit_3_aux := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |]
  &&  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  (store_int_array retval 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (3 > 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |]
  &&  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  (store_int_array retval 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_3 := clause_gen_binary_partial_solve_wit_3_pure -> clause_gen_binary_partial_solve_wit_3_aux.

Definition clause_gen_binary_partial_solve_wit_4_pure := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval_2: Z) (retval_3: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |]
  &&  ((( &( "clause4" ) )) # Ptr  |->_)
  **  (store_int_array retval 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval)
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_3)
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  ((( &( "clause1" ) )) # Ptr  |-> retval_2)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (3 > 0) |]
.

Definition clause_gen_binary_partial_solve_wit_4_aux := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) ,
  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |]
  &&  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  (store_int_array retval 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (3 > 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |]
  &&  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  (store_int_array retval 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_4 := clause_gen_binary_partial_solve_wit_4_pure -> clause_gen_binary_partial_solve_wit_4_aux.

Definition clause_gen_binary_partial_solve_wit_5 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  (store_int_array retval 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  (((retval + (0 * sizeof(INT) ) )) # Int  |->_)
  **  (store_int_array_missing_i_rec retval 0 0 3 (all_zero_list (3)) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_6 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  (store_int_array retval 3 (replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  (((retval + (1 * sizeof(INT) ) )) # Int  |->_)
  **  (store_int_array_missing_i_rec retval 1 0 3 (replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_7 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  (((retval_2 + (0 * sizeof(INT) ) )) # Int  |->_)
  **  (store_int_array_missing_i_rec retval_2 0 0 3 (all_zero_list (3)) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_8 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  (store_int_array retval_2 3 (replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  (((retval_2 + (1 * sizeof(INT) ) )) # Int  |->_)
  **  (store_int_array_missing_i_rec retval_2 1 0 3 (replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_9 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  (((retval_3 + (0 * sizeof(INT) ) )) # Int  |->_)
  **  (store_int_array_missing_i_rec retval_3 0 0 3 (all_zero_list (3)) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_10 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  (store_int_array retval_3 3 (replace_Znth (0) (p1_pre) ((all_zero_list (3)))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  (((retval_3 + (1 * sizeof(INT) ) )) # Int  |->_)
  **  (store_int_array_missing_i_rec retval_3 1 0 3 (replace_Znth (0) (p1_pre) ((all_zero_list (3)))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_11 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  (store_int_array retval_3 3 (replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  (((retval_3 + (2 * sizeof(INT) ) )) # Int  |->_)
  **  (store_int_array_missing_i_rec retval_3 2 0 3 (replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_12 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  (((retval_3 + (0 * sizeof(INT) ) )) # Int  |->_)
  **  (store_int_array_missing_i_rec retval_3 0 0 3 (all_zero_list (3)) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_13 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  (store_int_array retval_3 3 (replace_Znth (0) (p1_pre) ((all_zero_list (3)))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  (((retval_3 + (1 * sizeof(INT) ) )) # Int  |->_)
  **  (store_int_array_missing_i_rec retval_3 1 0 3 (replace_Znth (0) (p1_pre) ((all_zero_list (3)))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_14 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  (store_int_array retval 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  (((retval + (0 * sizeof(INT) ) )) # Int  |->_)
  **  (store_int_array_missing_i_rec retval 0 0 3 (all_zero_list (3)) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_15 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  (store_int_array retval 3 (replace_Znth (0) (p1_pre) ((all_zero_list (3)))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  (((retval + (1 * sizeof(INT) ) )) # Int  |->_)
  **  (store_int_array_missing_i_rec retval 1 0 3 (replace_Znth (0) (p1_pre) ((all_zero_list (3)))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_16 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  (((retval_2 + (0 * sizeof(INT) ) )) # Int  |->_)
  **  (store_int_array_missing_i_rec retval_2 0 0 3 (all_zero_list (3)) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_17 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  (store_int_array retval_2 3 (replace_Znth (0) (p2_pre) ((all_zero_list (3)))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  (((retval_2 + (1 * sizeof(INT) ) )) # Int  |->_)
  **  (store_int_array_missing_i_rec retval_2 1 0 3 (replace_Znth (0) (p2_pre) ((all_zero_list (3)))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_18 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  (((retval_3 + (0 * sizeof(INT) ) )) # Int  |->_)
  **  (store_int_array_missing_i_rec retval_3 0 0 3 (all_zero_list (3)) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_19 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  (store_int_array retval_3 3 (replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  (((retval_3 + (1 * sizeof(INT) ) )) # Int  |->_)
  **  (store_int_array_missing_i_rec retval_3 1 0 3 (replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_20 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  (store_int_array retval_3 3 (replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  (((retval_3 + (2 * sizeof(INT) ) )) # Int  |->_)
  **  (store_int_array_missing_i_rec retval_3 2 0 3 (replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_21 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  (((retval_3 + (0 * sizeof(INT) ) )) # Int  |->_)
  **  (store_int_array_missing_i_rec retval_3 0 0 3 (all_zero_list (3)) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_22 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  (store_int_array retval_3 3 (replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  (((retval_3 + (1 * sizeof(INT) ) )) # Int  |->_)
  **  (store_int_array_missing_i_rec retval_3 1 0 3 (replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_23 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  (store_int_array retval 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  (((retval + (0 * sizeof(INT) ) )) # Int  |->_)
  **  (store_int_array_missing_i_rec retval 0 0 3 (all_zero_list (3)) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_24 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  (store_int_array retval 3 (replace_Znth (0) (p1_pre) ((all_zero_list (3)))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  (((retval + (1 * sizeof(INT) ) )) # Int  |->_)
  **  (store_int_array_missing_i_rec retval 1 0 3 (replace_Znth (0) (p1_pre) ((all_zero_list (3)))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_25 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  (((retval_2 + (0 * sizeof(INT) ) )) # Int  |->_)
  **  (store_int_array_missing_i_rec retval_2 0 0 3 (all_zero_list (3)) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_26 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  (store_int_array retval_2 3 (replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  (((retval_2 + (1 * sizeof(INT) ) )) # Int  |->_)
  **  (store_int_array_missing_i_rec retval_2 1 0 3 (replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_27 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  (((retval_3 + (0 * sizeof(INT) ) )) # Int  |->_)
  **  (store_int_array_missing_i_rec retval_3 0 0 3 (all_zero_list (3)) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_28 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  (store_int_array retval_3 3 (replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  (((retval_3 + (1 * sizeof(INT) ) )) # Int  |->_)
  **  (store_int_array_missing_i_rec retval_3 1 0 3 (replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_29 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  (store_int_array retval_3 3 (replace_Znth (1) (p2_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  (((retval_3 + (2 * sizeof(INT) ) )) # Int  |->_)
  **  (store_int_array_missing_i_rec retval_3 2 0 3 (replace_Znth (1) (p2_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_30 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  (store_int_array retval 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  (((retval + (0 * sizeof(INT) ) )) # Int  |->_)
  **  (store_int_array_missing_i_rec retval 0 0 3 (all_zero_list (3)) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_31 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  (store_int_array retval 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  (((retval + (0 * sizeof(INT) ) )) # Int  |->_)
  **  (store_int_array_missing_i_rec retval 0 0 3 (all_zero_list (3)) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_32 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  (store_int_array retval 3 (replace_Znth (0) (p1_pre) ((all_zero_list (3)))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  (((retval + (1 * sizeof(INT) ) )) # Int  |->_)
  **  (store_int_array_missing_i_rec retval 1 0 3 (replace_Znth (0) (p1_pre) ((all_zero_list (3)))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_33 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  (store_int_array retval 3 (replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  (((retval + (2 * sizeof(INT) ) )) # Int  |->_)
  **  (store_int_array_missing_i_rec retval 2 0 3 (replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_34 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  (store_int_array retval 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  (((retval_2 + (0 * sizeof(INT) ) )) # Int  |->_)
  **  (store_int_array_missing_i_rec retval_2 0 0 3 (all_zero_list (3)) )
  **  (store_int_array retval 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_35 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  (store_int_array retval_2 3 (replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))) )
  **  (store_int_array retval 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  (((retval_2 + (1 * sizeof(INT) ) )) # Int  |->_)
  **  (store_int_array_missing_i_rec retval_2 1 0 3 (replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))) )
  **  (store_int_array retval 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_36 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  (store_int_array retval_2 3 (replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  (((retval_2 + (2 * sizeof(INT) ) )) # Int  |->_)
  **  (store_int_array_missing_i_rec retval_2 2 0 3 (replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_37 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  (store_int_array retval_2 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  (((retval_3 + (0 * sizeof(INT) ) )) # Int  |->_)
  **  (store_int_array_missing_i_rec retval_3 0 0 3 (all_zero_list (3)) )
  **  (store_int_array retval_2 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_38 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  (store_int_array retval_3 3 (replace_Znth (0) (p1_pre) ((all_zero_list (3)))) )
  **  (store_int_array retval_2 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  (((retval_3 + (1 * sizeof(INT) ) )) # Int  |->_)
  **  (store_int_array_missing_i_rec retval_3 1 0 3 (replace_Znth (0) (p1_pre) ((all_zero_list (3)))) )
  **  (store_int_array retval_2 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_39 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  (store_int_array retval_3 3 (replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  (((retval_3 + (2 * sizeof(INT) ) )) # Int  |->_)
  **  (store_int_array_missing_i_rec retval_3 2 0 3 (replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_40 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  (((retval_4 + (0 * sizeof(INT) ) )) # Int  |->_)
  **  (store_int_array_missing_i_rec retval_4 0 0 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_41 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  (store_int_array retval_4 3 (replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))) )
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  (((retval_4 + (1 * sizeof(INT) ) )) # Int  |->_)
  **  (store_int_array_missing_i_rec retval_4 1 0 3 (replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))) )
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_42 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  (store_int_array retval_4 3 (replace_Znth (1) (p2_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  (((retval_4 + (2 * sizeof(INT) ) )) # Int  |->_)
  **  (store_int_array_missing_i_rec retval_4 2 0 3 (replace_Znth (1) (p2_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_43 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  (store_int_array retval 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  (((retval + (0 * sizeof(INT) ) )) # Int  |->_)
  **  (store_int_array_missing_i_rec retval 0 0 3 (all_zero_list (3)) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_44 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  (store_int_array retval_3 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  (store_int_array retval_3 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_45 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_46 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  (store_int_array retval_3 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  (store_int_array retval_3 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_47 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  (store_int_array retval_3 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  (store_int_array retval_3 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_48 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_49 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  (store_int_array retval 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  (store_int_array retval 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_50 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  (store_int_array retval_4 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  (store_int_array retval_4 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_51 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  (store_int_array retval 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  (store_int_array retval 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_52 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) ,
  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_53 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) ,
  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval_4 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval_4 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_54 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) ,
  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_55 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) ,
  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_56 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) ,
  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval_3 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval_3 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_57 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) ,
  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval_3 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval_3 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_58 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) ,
  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_59 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) ,
  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval_3 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval_3 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_60 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) ,
  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval_3 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval_3 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_61 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) ,
  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_62 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) ,
  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval_3 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval_3 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_63 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) ,
  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval_3 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval_3 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_64 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) ,
  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_65 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) ,
  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_66 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) ,
  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval_4 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval_4 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_67 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) ,
  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_68 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) ,
  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_69 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) ,
  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval_4 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval_4 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_70 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) ,
  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_71 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) ,
  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_72 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) ,
  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval_3 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval_3 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_73 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) ,
  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval_3 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval_3 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_74 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) ,
  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_75 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) ,
  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval_3 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval_3 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition clause_gen_binary_partial_solve_wit_76 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) ,
  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  (store_predata data_pre clist pcnt ccnt )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
.

Definition clause_gen_binary_partial_solve_wit_77 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) ,
  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval_4 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  (store_predata data_pre clist pcnt ccnt )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval_4 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
.

Definition clause_gen_binary_partial_solve_wit_78 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) ,
  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  (store_predata data_pre clist pcnt ccnt )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
.

Definition clause_gen_binary_partial_solve_wit_79 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) ,
  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  (store_predata data_pre clist pcnt ccnt )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
.

Definition clause_gen_binary_partial_solve_wit_80 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) ,
  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval_3 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  (store_predata data_pre clist pcnt ccnt )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval_3 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
.

Definition clause_gen_binary_partial_solve_wit_81 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) ,
  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval_3 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  (store_predata data_pre clist pcnt ccnt )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval_3 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
.

Definition clause_gen_binary_partial_solve_wit_82 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) ,
  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  (store_predata data_pre clist pcnt ccnt )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
.

Definition clause_gen_binary_partial_solve_wit_83 := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) ,
  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval_3 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  (store_predata data_pre clist pcnt ccnt )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_int_array retval_3 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
.

Definition clause_gen_binary_partial_solve_wit_84_pure := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval_2: Z) (retval: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 1 ) = 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 1 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_2 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 1 ))
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  (store_int_array retval 3 (all_zero_list (3)) )
  **  ((( &( "clause2" ) )) # Ptr  |-> retval)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval_2)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| (retval <> 0) |] 
  &&  [| (3 > 0) |]
.

Definition clause_gen_binary_partial_solve_wit_84_aux := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 1 ) = 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 1 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  (store_int_array retval 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
|--
  [| (retval_2 <> 0) |] 
  &&  [| (3 > 0) |] 
  &&  [| ((0 + 1 ) = 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 1 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  (store_int_array retval 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
.

Definition clause_gen_binary_partial_solve_wit_84 := clause_gen_binary_partial_solve_wit_84_pure -> clause_gen_binary_partial_solve_wit_84_aux.

Definition clause_gen_binary_partial_solve_wit_85_pure := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval_2: Z) (retval: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 1 ) = 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 1 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_2 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 1 ))
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_3)
  **  (store_int_array retval 3 (all_zero_list (3)) )
  **  ((( &( "clause2" ) )) # Ptr  |-> retval)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval_2)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| (retval <> 0) |] 
  &&  [| (3 > 0) |]
.

Definition clause_gen_binary_partial_solve_wit_85_aux := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 1 ) = 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 1 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  (store_int_array retval 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  (store_int_array retval_2 3 (all_zero_list (3)) )
|--
  [| (retval_2 <> 0) |] 
  &&  [| (3 > 0) |] 
  &&  [| ((0 + 1 ) = 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  (store_int_array retval_2 3 (all_zero_list (3)) )
  **  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 1 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  (store_int_array retval 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
.

Definition clause_gen_binary_partial_solve_wit_85 := clause_gen_binary_partial_solve_wit_85_pure -> clause_gen_binary_partial_solve_wit_85_aux.

Definition clause_gen_binary_partial_solve_wit_86_pure := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval_2: Z) (retval_3: Z) (retval: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 1 ) = 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 1 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_2 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 1 ))
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  (store_int_array retval 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval_2)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| (retval <> 0) |] 
  &&  [| (3 > 0) |]
.

Definition clause_gen_binary_partial_solve_wit_86_aux := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 1 ) = 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 1 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  (store_int_array retval 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
|--
  [| (retval_3 <> 0) |] 
  &&  [| (3 > 0) |] 
  &&  [| ((0 + 1 ) = 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 1 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  (store_int_array retval 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
.

Definition clause_gen_binary_partial_solve_wit_86 := clause_gen_binary_partial_solve_wit_86_pure -> clause_gen_binary_partial_solve_wit_86_aux.

Definition clause_gen_binary_partial_solve_wit_87_pure := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval_2: Z) (retval_3: Z) (retval: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 1 ) = 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 1 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_2 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 1 ))
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_4)
  **  (store_int_array retval 3 (all_zero_list (3)) )
  **  ((( &( "clause3" ) )) # Ptr  |-> retval)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval_2)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| (retval <> 0) |] 
  &&  [| (3 > 0) |]
.

Definition clause_gen_binary_partial_solve_wit_87_aux := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 1 ) = 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 1 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  (store_int_array retval 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  (store_int_array retval_3 3 (all_zero_list (3)) )
|--
  [| (retval_3 <> 0) |] 
  &&  [| (3 > 0) |] 
  &&  [| ((0 + 1 ) = 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  (store_int_array retval_3 3 (all_zero_list (3)) )
  **  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 1 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  (store_int_array retval 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
.

Definition clause_gen_binary_partial_solve_wit_87 := clause_gen_binary_partial_solve_wit_87_pure -> clause_gen_binary_partial_solve_wit_87_aux.

Definition clause_gen_binary_partial_solve_wit_88_pure := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 1 ) = 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 1 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_2 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 1 ))
  **  (store_int_array retval 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval_2)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| (retval <> 0) |] 
  &&  [| (3 > 0) |]
.

Definition clause_gen_binary_partial_solve_wit_88_aux := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 1 ) = 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 1 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  (store_int_array retval 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
|--
  [| (retval_4 <> 0) |] 
  &&  [| (3 > 0) |] 
  &&  [| ((0 + 1 ) = 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 1 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  (store_int_array retval 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
.

Definition clause_gen_binary_partial_solve_wit_88 := clause_gen_binary_partial_solve_wit_88_pure -> clause_gen_binary_partial_solve_wit_88_aux.

Definition clause_gen_binary_partial_solve_wit_89_pure := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 1 ) = 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 1 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_2 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 1 ))
  **  (store_int_array retval 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval_2)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| (retval <> 0) |] 
  &&  [| (3 > 0) |]
.

Definition clause_gen_binary_partial_solve_wit_89_aux := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 1 ) = 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 1 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  (store_int_array retval 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
|--
  [| (retval_4 <> 0) |] 
  &&  [| (3 > 0) |] 
  &&  [| ((0 + 1 ) = 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 1 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  (store_int_array retval 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
.

Definition clause_gen_binary_partial_solve_wit_89 := clause_gen_binary_partial_solve_wit_89_pure -> clause_gen_binary_partial_solve_wit_89_aux.

Definition clause_gen_binary_partial_solve_wit_90_pure := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 1 ) = 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_6)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 1 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_5)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list2" ) )) # Ptr  |-> retval)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_6)
  **  (store_int_array retval_2 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 1 ))
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_5)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval_2)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| (retval <> 0) |]
.

Definition clause_gen_binary_partial_solve_wit_90_aux := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 1 ) = 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 1 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  (store_int_array retval 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
|--
  [| (retval_6 <> 0) |] 
  &&  [| ((0 + 1 ) = 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 1 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  (store_int_array retval 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
.

Definition clause_gen_binary_partial_solve_wit_90 := clause_gen_binary_partial_solve_wit_90_pure -> clause_gen_binary_partial_solve_wit_90_aux.

Definition clause_gen_binary_partial_solve_wit_91_pure := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 1 ) = 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_6)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 1 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_5)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list2" ) )) # Ptr  |-> retval)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_6)
  **  (store_int_array retval_2 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 1 ))
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_5)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval_2)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| (retval <> 0) |]
.

Definition clause_gen_binary_partial_solve_wit_91_aux := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 1 ) = 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 1 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  (store_int_array retval 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
|--
  [| (retval_6 <> 0) |] 
  &&  [| ((0 + 1 ) = 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 1 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  (store_int_array retval 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
.

Definition clause_gen_binary_partial_solve_wit_91 := clause_gen_binary_partial_solve_wit_91_pure -> clause_gen_binary_partial_solve_wit_91_aux.

Definition clause_gen_binary_partial_solve_wit_92_pure := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 1 ) = 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_6)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 1 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_5)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list3" ) )) # Ptr  |-> retval)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_6)
  **  (store_int_array retval_2 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 1 ))
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_5)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval_2)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| (retval <> 0) |]
.

Definition clause_gen_binary_partial_solve_wit_92_aux := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 1 ) = 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 1 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  (store_int_array retval 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
|--
  [| (retval_7 <> 0) |] 
  &&  [| ((0 + 1 ) = 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 1 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  (store_int_array retval 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
.

Definition clause_gen_binary_partial_solve_wit_92 := clause_gen_binary_partial_solve_wit_92_pure -> clause_gen_binary_partial_solve_wit_92_aux.

Definition clause_gen_binary_partial_solve_wit_93_pure := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 1 ) = 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_6)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 1 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_5)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list3" ) )) # Ptr  |-> retval)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_6)
  **  (store_int_array retval_2 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 1 ))
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_5)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval_2)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| (retval <> 0) |]
.

Definition clause_gen_binary_partial_solve_wit_93_aux := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 1 ) = 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 1 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  (store_int_array retval 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
|--
  [| (retval_7 <> 0) |] 
  &&  [| ((0 + 1 ) = 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 1 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  (store_int_array retval 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
.

Definition clause_gen_binary_partial_solve_wit_93 := clause_gen_binary_partial_solve_wit_93_pure -> clause_gen_binary_partial_solve_wit_93_aux.

Definition clause_gen_binary_partial_solve_wit_94_pure := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (retval: Z) (y: Z) ,
  [| ((0 + 1 ) = 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_6)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 1 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_5)
  **  ((&((retval)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_8)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_6)
  **  (store_int_array retval_2 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 1 ))
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_5)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval_2)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| (retval <> 0) |]
.

Definition clause_gen_binary_partial_solve_wit_94_aux := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 1 ) = 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 1 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  (store_int_array retval 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
|--
  [| (retval_8 <> 0) |] 
  &&  [| ((0 + 1 ) = 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 1 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  (store_int_array retval 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
.

Definition clause_gen_binary_partial_solve_wit_94 := clause_gen_binary_partial_solve_wit_94_pure -> clause_gen_binary_partial_solve_wit_94_aux.

Definition clause_gen_binary_partial_solve_wit_95_pure := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (retval: Z) (y: Z) ,
  [| ((0 + 1 ) = 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_6)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 1 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_5)
  **  ((&((retval)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_8)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_6)
  **  (store_int_array retval_2 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 1 ))
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_5)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval_2)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| (retval <> 0) |]
.

Definition clause_gen_binary_partial_solve_wit_95_aux := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 1 ) = 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 1 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  (store_int_array retval 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
|--
  [| (retval_8 <> 0) |] 
  &&  [| ((0 + 1 ) = 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre <> 2) |] 
  &&  [| (op_pre = 3) |]
  &&  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 1 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  (store_int_array retval 3 (replace_Znth (0) (p3_pre) ((all_zero_list (3)))) )
.

Definition clause_gen_binary_partial_solve_wit_95 := clause_gen_binary_partial_solve_wit_95_pure -> clause_gen_binary_partial_solve_wit_95_aux.

Definition clause_gen_binary_partial_solve_wit_96_pure := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 3 ) = 3) |] 
  &&  [| ((0 + 3 ) <> 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 3 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_7)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_6)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_4 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_3 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 3 ))
  **  (store_int_array retval 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval_2)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| (retval <> 0) |] 
  &&  [| (3 > 0) |]
.

Definition clause_gen_binary_partial_solve_wit_96_aux := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 3 ) = 3) |] 
  &&  [| ((0 + 3 ) <> 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 3 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_7)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_6)
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
|--
  [| (retval_4 <> 0) |] 
  &&  [| (3 > 0) |] 
  &&  [| ((0 + 3 ) = 3) |] 
  &&  [| ((0 + 3 ) <> 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 3 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_7)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_6)
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
.

Definition clause_gen_binary_partial_solve_wit_96 := clause_gen_binary_partial_solve_wit_96_pure -> clause_gen_binary_partial_solve_wit_96_aux.

Definition clause_gen_binary_partial_solve_wit_97_pure := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 3 ) = 3) |] 
  &&  [| ((0 + 3 ) <> 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 3 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_7)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_6)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_4 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_3 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 3 ))
  **  (store_int_array retval 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval_2)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| (retval <> 0) |] 
  &&  [| (3 > 0) |]
.

Definition clause_gen_binary_partial_solve_wit_97_aux := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 3 ) = 3) |] 
  &&  [| ((0 + 3 ) <> 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 3 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_7)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_6)
  **  (store_int_array retval_3 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
|--
  [| (retval_4 <> 0) |] 
  &&  [| (3 > 0) |] 
  &&  [| ((0 + 3 ) = 3) |] 
  &&  [| ((0 + 3 ) <> 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 3 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_7)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_6)
  **  (store_int_array retval_3 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
.

Definition clause_gen_binary_partial_solve_wit_97 := clause_gen_binary_partial_solve_wit_97_pure -> clause_gen_binary_partial_solve_wit_97_aux.

Definition clause_gen_binary_partial_solve_wit_98_pure := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 3 ) = 3) |] 
  &&  [| ((0 + 3 ) <> 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 3 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_7)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_6)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_4 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_3 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 3 ))
  **  (store_int_array retval 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval_2)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| (retval <> 0) |] 
  &&  [| (3 > 0) |]
.

Definition clause_gen_binary_partial_solve_wit_98_aux := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 3 ) = 3) |] 
  &&  [| ((0 + 3 ) <> 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 3 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_7)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_6)
  **  (store_int_array retval_3 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
|--
  [| (retval_4 <> 0) |] 
  &&  [| (3 > 0) |] 
  &&  [| ((0 + 3 ) = 3) |] 
  &&  [| ((0 + 3 ) <> 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 3 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_7)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_6)
  **  (store_int_array retval_3 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
.

Definition clause_gen_binary_partial_solve_wit_98 := clause_gen_binary_partial_solve_wit_98_pure -> clause_gen_binary_partial_solve_wit_98_aux.

Definition clause_gen_binary_partial_solve_wit_99_pure := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 3 ) = 3) |] 
  &&  [| ((0 + 3 ) <> 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 3 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_7)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_6)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_4 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_3 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 3 ))
  **  (store_int_array retval 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval_2)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| (retval <> 0) |] 
  &&  [| (3 > 0) |]
.

Definition clause_gen_binary_partial_solve_wit_99_aux := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 3 ) = 3) |] 
  &&  [| ((0 + 3 ) <> 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 3 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_7)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_6)
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
|--
  [| (retval_4 <> 0) |] 
  &&  [| (3 > 0) |] 
  &&  [| ((0 + 3 ) = 3) |] 
  &&  [| ((0 + 3 ) <> 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 3 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_7)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_6)
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
.

Definition clause_gen_binary_partial_solve_wit_99 := clause_gen_binary_partial_solve_wit_99_pure -> clause_gen_binary_partial_solve_wit_99_aux.

Definition clause_gen_binary_partial_solve_wit_100_pure := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 3 ) = 3) |] 
  &&  [| ((0 + 3 ) <> 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 3 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_7)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_6)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_6)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_5)
  **  (store_int_array retval_4 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_3 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 3 ))
  **  (store_int_array retval 3 (all_zero_list (3)) )
  **  ((( &( "clause4" ) )) # Ptr  |-> retval)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval_2)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| (retval <> 0) |] 
  &&  [| (3 > 0) |]
.

Definition clause_gen_binary_partial_solve_wit_100_aux := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 3 ) = 3) |] 
  &&  [| ((0 + 3 ) <> 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 3 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_7)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_6)
  **  (store_int_array retval_3 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_4 3 (all_zero_list (3)) )
|--
  [| (retval_4 <> 0) |] 
  &&  [| (3 > 0) |] 
  &&  [| ((0 + 3 ) = 3) |] 
  &&  [| ((0 + 3 ) <> 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  (store_int_array retval_4 3 (all_zero_list (3)) )
  **  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 3 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_7)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_6)
  **  (store_int_array retval_3 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
.

Definition clause_gen_binary_partial_solve_wit_100 := clause_gen_binary_partial_solve_wit_100_pure -> clause_gen_binary_partial_solve_wit_100_aux.

Definition clause_gen_binary_partial_solve_wit_101_pure := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (retval: Z) (y: Z) ,
  [| ((0 + 3 ) = 3) |] 
  &&  [| ((0 + 3 ) <> 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_6)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 3 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_5)
  **  ((&((retval)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_8)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_7)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_6)
  **  (store_int_array retval_4 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_3 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 3 ))
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_5)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval_2)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| (retval <> 0) |]
.

Definition clause_gen_binary_partial_solve_wit_101_aux := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 3 ) = 3) |] 
  &&  [| ((0 + 3 ) <> 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 3 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_7)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_6)
  **  (store_int_array retval_3 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
|--
  [| (retval_8 <> 0) |] 
  &&  [| ((0 + 3 ) = 3) |] 
  &&  [| ((0 + 3 ) <> 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 3 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_7)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_6)
  **  (store_int_array retval_3 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
.

Definition clause_gen_binary_partial_solve_wit_101 := clause_gen_binary_partial_solve_wit_101_pure -> clause_gen_binary_partial_solve_wit_101_aux.

Definition clause_gen_binary_partial_solve_wit_102_pure := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (retval: Z) (y: Z) ,
  [| ((0 + 3 ) = 3) |] 
  &&  [| ((0 + 3 ) <> 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_6)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 3 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_5)
  **  ((&((retval)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_8)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_7)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_6)
  **  (store_int_array retval_4 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_3 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 3 ))
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_5)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval_2)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| (retval <> 0) |]
.

Definition clause_gen_binary_partial_solve_wit_102_aux := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 3 ) = 3) |] 
  &&  [| ((0 + 3 ) <> 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 3 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_7)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_6)
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
|--
  [| (retval_8 <> 0) |] 
  &&  [| ((0 + 3 ) = 3) |] 
  &&  [| ((0 + 3 ) <> 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre = 1) |]
  &&  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 3 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_7)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_6)
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
.

Definition clause_gen_binary_partial_solve_wit_102 := clause_gen_binary_partial_solve_wit_102_pure -> clause_gen_binary_partial_solve_wit_102_aux.

Definition clause_gen_binary_partial_solve_wit_103_pure := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (retval: Z) (y: Z) ,
  [| ((0 + 3 ) = 3) |] 
  &&  [| ((0 + 3 ) <> 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_6)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 3 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_5)
  **  ((&((retval)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_8)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_7)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_6)
  **  (store_int_array retval_4 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_3 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 3 ))
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_5)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval_2)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| (retval <> 0) |]
.

Definition clause_gen_binary_partial_solve_wit_103_aux := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 3 ) = 3) |] 
  &&  [| ((0 + 3 ) <> 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 3 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_7)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_6)
  **  (store_int_array retval_3 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
|--
  [| (retval_8 <> 0) |] 
  &&  [| ((0 + 3 ) = 3) |] 
  &&  [| ((0 + 3 ) <> 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre = p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 3 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_7)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_6)
  **  (store_int_array retval_3 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
.

Definition clause_gen_binary_partial_solve_wit_103 := clause_gen_binary_partial_solve_wit_103_pure -> clause_gen_binary_partial_solve_wit_103_aux.

Definition clause_gen_binary_partial_solve_wit_104_pure := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (retval: Z) (y: Z) ,
  [| ((0 + 3 ) = 3) |] 
  &&  [| ((0 + 3 ) <> 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_6)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 3 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_5)
  **  ((&((retval)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_8)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_7)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_6)
  **  (store_int_array retval_4 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_3 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 3 ))
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_5)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval_2)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| (retval <> 0) |]
.

Definition clause_gen_binary_partial_solve_wit_104_aux := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 3 ) = 3) |] 
  &&  [| ((0 + 3 ) <> 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 3 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_7)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_6)
  **  (store_int_array retval_3 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
|--
  [| (retval_8 <> 0) |] 
  &&  [| ((0 + 3 ) = 3) |] 
  &&  [| ((0 + 3 ) <> 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre = 0) |]
  &&  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 3 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_7)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_6)
  **  (store_int_array retval_3 3 (replace_Znth (2) (p3_pre) ((replace_Znth (1) ((-p2_pre)) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p2_pre) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) ((-p3_pre)) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
.

Definition clause_gen_binary_partial_solve_wit_104 := clause_gen_binary_partial_solve_wit_104_pure -> clause_gen_binary_partial_solve_wit_104_aux.

Definition clause_gen_binary_partial_solve_wit_105_pure := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (retval: Z) (y: Z) ,
  [| ((0 + 3 ) = 3) |] 
  &&  [| ((0 + 3 ) <> 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_6)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 3 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_5)
  **  ((&((retval)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "list4" ) )) # Ptr  |-> retval)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "list3" ) )) # Ptr  |-> retval_8)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_8)
  **  ((( &( "list2" ) )) # Ptr  |-> retval_7)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_7)
  **  ((( &( "list1" ) )) # Ptr  |-> retval_6)
  **  (store_int_array retval_4 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_3 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
  **  ((( &( "cnt" ) )) # Int  |-> (0 + 3 ))
  **  ((( &( "clause4" ) )) # Ptr  |-> retval_5)
  **  ((( &( "clause3" ) )) # Ptr  |-> retval_4)
  **  ((( &( "clause2" ) )) # Ptr  |-> retval_3)
  **  ((( &( "clause1" ) )) # Ptr  |-> retval_2)
  **  ((( &( "size" ) )) # Int  |-> 3)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "p3" ) )) # Int  |-> p3_pre)
  **  ((( &( "p2" ) )) # Int  |-> p2_pre)
  **  ((( &( "p1" ) )) # Int  |-> p1_pre)
|--
  [| (retval <> 0) |]
.

Definition clause_gen_binary_partial_solve_wit_105_aux := 
forall (data_pre: Z) (op_pre: Z) (p3_pre: Z) (p2_pre: Z) (p1_pre: Z) (bop: SmtPropBop) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (y: Z) ,
  [| ((0 + 3 ) = 3) |] 
  &&  [| ((0 + 3 ) <> 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 3 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_7)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_6)
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
|--
  [| (retval_8 <> 0) |] 
  &&  [| ((0 + 3 ) = 3) |] 
  &&  [| ((0 + 3 ) <> 2) |] 
  &&  [| ((0 + 3 ) <> 1) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |] 
  &&  [| (retval_8 <> 0) |] 
  &&  [| (retval_7 <> 0) |] 
  &&  [| (retval_6 <> 0) |] 
  &&  [| (retval_5 <> 0) |] 
  &&  [| (p1_pre <> p2_pre) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (p1_pre <> 0) |] 
  &&  [| (p2_pre <> 0) |] 
  &&  [| (p3_pre <> 0) |] 
  &&  [| (p1_pre <= pcnt) |] 
  &&  [| (p2_pre <= pcnt) |] 
  &&  [| (p3_pre <= pcnt) |] 
  &&  [| ((-p1_pre) <= pcnt) |] 
  &&  [| ((-p2_pre) <= pcnt) |] 
  &&  [| ((-p3_pre) <= pcnt) |] 
  &&  [| (((prop_cnt_inf (clist)) + 1 ) <= pcnt) |] 
  &&  [| (op_pre = (SmtPBID (bop))) |] 
  &&  [| (op_pre <> 1) |] 
  &&  [| (op_pre <> 0) |] 
  &&  [| (op_pre = 2) |]
  &&  ((&((retval_8)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_4)
  **  ((&((retval_8)  # "cnf_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> retval_5)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> (ccnt + 3 ))
  **  (sll_cnf_list y clist )
  **  ((&((retval_7)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_3)
  **  ((&((retval_7)  # "cnf_list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval_2)
  **  ((&((retval_6)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_7)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "size")) # Int  |-> 3)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "clause")) # Ptr  |-> retval)
  **  ((&((retval_5)  # "cnf_list" ->ₛ "next")) # Ptr  |-> retval_6)
  **  (store_int_array retval_3 3 (replace_Znth (2) ((-p3_pre)) ((replace_Znth (1) (p2_pre) ((replace_Znth (0) ((-p1_pre)) ((all_zero_list (3)))))))) )
  **  (store_int_array retval_2 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) ((-p2_pre)) ((all_zero_list (3)))))) )
  **  (store_int_array retval 3 (replace_Znth (1) (p3_pre) ((replace_Znth (0) (p1_pre) ((all_zero_list (3)))))) )
.

Definition clause_gen_binary_partial_solve_wit_105 := clause_gen_binary_partial_solve_wit_105_pure -> clause_gen_binary_partial_solve_wit_105_aux.

Definition clause_gen_binary_which_implies_wit_1 := 
forall (data_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) ,
  (store_predata data_pre clist pcnt ccnt )
|--
  EX (y: Z) ,
  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist)) = ccnt) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y)
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt)
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt)
  **  (sll_cnf_list y clist )
.

(*----- Function prop2cnf -----*)

Definition prop2cnf_safety_wit_1 := 
forall (data_pre: Z) (p_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (prop: smt_prop) ,
  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |]
  &&  ((( &( "res" ) )) # Int  |->_)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (store_SmtProp p_pre prop )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition prop2cnf_safety_wit_2 := 
forall (data_pre: Z) (p_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (prop: smt_prop) (t: Z) ,
  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |]
  &&  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> t)
  **  (store_SmtProp' p_pre prop )
  **  ((( &( "res" ) )) # Int  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (5 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 5) |]
.

Definition prop2cnf_safety_wit_3 := 
forall (data_pre: Z) (p_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (prop: smt_prop) (t: Z) (z: Z) (y: Z) (op: SmtPropBop) (lt: smt_prop) (rt: smt_prop) (clist': (@list (@list Z))) (pcnt': Z) (ccnt': Z) (res: Z) (retval: Z) (clist'_2: (@list (@list Z))) (pcnt'_2: Z) (ccnt'_2: Z) (res_2: Z) (retval_2: Z) (clist'': (@list (@list Z))) (pcnt'': Z) (ccnt'': Z) (y'': Z) ,
  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist'')) = ccnt'') |] 
  &&  [| ((prop_cnt_inf (clist'')) <= pcnt'') |] 
  &&  [| (pcnt'' >= 0) |] 
  &&  [| ((make_prop2cnf_ret ((make_predata (clist'_2) (pcnt'_2) (ccnt'_2))) (res_2)) = (prop2cnf_logic (rt) ((make_predata (clist') (pcnt') (ccnt'))))) |] 
  &&  [| (retval_2 = res_2) |] 
  &&  [| (res_2 <> 0) |] 
  &&  [| (res_2 <= pcnt'_2) |] 
  &&  [| ((-res_2) <= pcnt'_2) |] 
  &&  [| ((make_prop2cnf_ret ((make_predata (clist') (pcnt') (ccnt'))) (res)) = (prop2cnf_logic (lt) ((make_predata (clist) (pcnt) (ccnt))))) |] 
  &&  [| (retval = res) |] 
  &&  [| (res <> 0) |] 
  &&  [| (res <= pcnt') |] 
  &&  [| ((-res) <= pcnt') |] 
  &&  [| ((prop_cnt_inf_SmtProp (lt)) <= pcnt) |] 
  &&  [| ((prop_cnt_inf_SmtProp (rt)) <= pcnt) |] 
  &&  [| (prop = (SmtB (op) (lt) (rt))) |] 
  &&  [| (p_pre <> 0) |] 
  &&  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t = 5) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y'')
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt'')
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt'')
  **  (sll_cnf_list y'' clist'' )
  **  (store_SmtProp z rt )
  **  ((( &( "p2" ) )) # Int  |-> retval_2)
  **  (store_SmtProp y lt )
  **  ((( &( "p1" ) )) # Int  |-> retval)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "op")) # Int  |-> (SmtPBID (op)))
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop1")) # Ptr  |-> y)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop2")) # Ptr  |-> z)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
  **  ((( &( "res" ) )) # Int  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
|--
  [| ((pcnt'' + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (pcnt'' + 1 )) |]
.

Definition prop2cnf_safety_wit_4 := 
forall (data_pre: Z) (p_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (prop: smt_prop) (t: Z) (z: Z) (y: Z) (op: SmtPropBop) (lt: smt_prop) (rt: smt_prop) (clist': (@list (@list Z))) (pcnt': Z) (ccnt': Z) (res: Z) (retval: Z) (clist'_2: (@list (@list Z))) (pcnt'_2: Z) (ccnt'_2: Z) (res_2: Z) (retval_2: Z) (clist'': (@list (@list Z))) (pcnt'': Z) (ccnt'': Z) (y'': Z) ,
  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist'')) = ccnt'') |] 
  &&  [| ((prop_cnt_inf (clist'')) <= pcnt'') |] 
  &&  [| (pcnt'' >= 0) |] 
  &&  [| ((make_prop2cnf_ret ((make_predata (clist'_2) (pcnt'_2) (ccnt'_2))) (res_2)) = (prop2cnf_logic (rt) ((make_predata (clist') (pcnt') (ccnt'))))) |] 
  &&  [| (retval_2 = res_2) |] 
  &&  [| (res_2 <> 0) |] 
  &&  [| (res_2 <= pcnt'_2) |] 
  &&  [| ((-res_2) <= pcnt'_2) |] 
  &&  [| ((make_prop2cnf_ret ((make_predata (clist') (pcnt') (ccnt'))) (res)) = (prop2cnf_logic (lt) ((make_predata (clist) (pcnt) (ccnt))))) |] 
  &&  [| (retval = res) |] 
  &&  [| (res <> 0) |] 
  &&  [| (res <= pcnt') |] 
  &&  [| ((-res) <= pcnt') |] 
  &&  [| ((prop_cnt_inf_SmtProp (lt)) <= pcnt) |] 
  &&  [| ((prop_cnt_inf_SmtProp (rt)) <= pcnt) |] 
  &&  [| (prop = (SmtB (op) (lt) (rt))) |] 
  &&  [| (p_pre <> 0) |] 
  &&  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t = 5) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y'')
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt'')
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt'')
  **  (sll_cnf_list y'' clist'' )
  **  (store_SmtProp z rt )
  **  ((( &( "p2" ) )) # Int  |-> retval_2)
  **  (store_SmtProp y lt )
  **  ((( &( "p1" ) )) # Int  |-> retval)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "op")) # Int  |-> (SmtPBID (op)))
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop1")) # Ptr  |-> y)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop2")) # Ptr  |-> z)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
  **  ((( &( "res" ) )) # Int  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition prop2cnf_safety_wit_5 := 
forall (data_pre: Z) (p_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (prop: smt_prop) (t: Z) ,
  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t <> 5) |]
  &&  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> t)
  **  (store_SmtProp' p_pre prop )
  **  ((( &( "res" ) )) # Int  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (6 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 6) |]
.

Definition prop2cnf_safety_wit_6 := 
forall (data_pre: Z) (p_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (prop: smt_prop) (t: Z) (y: Z) (op: SmtPropUop) (sub_prop: smt_prop) (clist': (@list (@list Z))) (pcnt': Z) (ccnt': Z) (res: Z) (retval: Z) (clist'': (@list (@list Z))) (pcnt'': Z) (ccnt'': Z) (y'': Z) ,
  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist'')) = ccnt'') |] 
  &&  [| ((prop_cnt_inf (clist'')) <= pcnt'') |] 
  &&  [| (pcnt'' >= 0) |] 
  &&  [| ((make_prop2cnf_ret ((make_predata (clist') (pcnt') (ccnt'))) (res)) = (prop2cnf_logic (sub_prop) ((make_predata (clist) (pcnt) (ccnt))))) |] 
  &&  [| (retval = res) |] 
  &&  [| (res <> 0) |] 
  &&  [| (res <= pcnt') |] 
  &&  [| ((-res) <= pcnt') |] 
  &&  [| ((prop_cnt_inf_SmtProp (sub_prop)) <= pcnt) |] 
  &&  [| (prop = (SmtU (op) (sub_prop))) |] 
  &&  [| (p_pre <> 0) |] 
  &&  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t <> 5) |] 
  &&  [| (t = 6) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y'')
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt'')
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt'')
  **  (sll_cnf_list y'' clist'' )
  **  (store_SmtProp y sub_prop )
  **  ((( &( "p1" ) )) # Int  |-> retval)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "op")) # Int  |-> (SmtPUID (op)))
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "prop1")) # Ptr  |-> y)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
  **  ((( &( "res" ) )) # Int  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
|--
  [| ((pcnt'' + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (pcnt'' + 1 )) |]
.

Definition prop2cnf_safety_wit_7 := 
forall (data_pre: Z) (p_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (prop: smt_prop) (t: Z) (y: Z) (op: SmtPropUop) (sub_prop: smt_prop) (clist': (@list (@list Z))) (pcnt': Z) (ccnt': Z) (res: Z) (retval: Z) (clist'': (@list (@list Z))) (pcnt'': Z) (ccnt'': Z) (y'': Z) ,
  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist'')) = ccnt'') |] 
  &&  [| ((prop_cnt_inf (clist'')) <= pcnt'') |] 
  &&  [| (pcnt'' >= 0) |] 
  &&  [| ((make_prop2cnf_ret ((make_predata (clist') (pcnt') (ccnt'))) (res)) = (prop2cnf_logic (sub_prop) ((make_predata (clist) (pcnt) (ccnt))))) |] 
  &&  [| (retval = res) |] 
  &&  [| (res <> 0) |] 
  &&  [| (res <= pcnt') |] 
  &&  [| ((-res) <= pcnt') |] 
  &&  [| ((prop_cnt_inf_SmtProp (sub_prop)) <= pcnt) |] 
  &&  [| (prop = (SmtU (op) (sub_prop))) |] 
  &&  [| (p_pre <> 0) |] 
  &&  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t <> 5) |] 
  &&  [| (t = 6) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y'')
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt'')
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt'')
  **  (sll_cnf_list y'' clist'' )
  **  (store_SmtProp y sub_prop )
  **  ((( &( "p1" ) )) # Int  |-> retval)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "op")) # Int  |-> (SmtPUID (op)))
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "prop1")) # Ptr  |-> y)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
  **  ((( &( "res" ) )) # Int  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition prop2cnf_safety_wit_8 := 
forall (data_pre: Z) (p_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (prop: smt_prop) (t: Z) ,
  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t <> 5) |] 
  &&  [| (t <> 6) |]
  &&  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> t)
  **  (store_SmtProp' p_pre prop )
  **  ((( &( "res" ) )) # Int  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (7 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 7) |]
.

Definition prop2cnf_safety_wit_9 := 
forall (data_pre: Z) (p_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (prop: smt_prop) (t: Z) ,
  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t <> 5) |] 
  &&  [| (t <> 6) |] 
  &&  [| (t <> 7) |]
  &&  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> t)
  **  (store_SmtProp' p_pre prop )
  **  ((( &( "res" ) )) # Int  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| False |]
.

Definition prop2cnf_entail_wit_1 := 
forall (data_pre: Z) (p_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (prop: smt_prop) (t: Z) (z: Z) (y: Z) (op: SmtPropBop) (lt: smt_prop) (rt: smt_prop) (clist': (@list (@list Z))) (pcnt': Z) (ccnt': Z) (res: Z) (retval: Z) (clist'_2: (@list (@list Z))) (pcnt'_2: Z) (ccnt'_2: Z) (res_2: Z) (retval_2: Z) ,
  [| ((make_prop2cnf_ret ((make_predata (clist'_2) (pcnt'_2) (ccnt'_2))) (res_2)) = (prop2cnf_logic (rt) ((make_predata (clist') (pcnt') (ccnt'))))) |] 
  &&  [| (retval_2 = res_2) |] 
  &&  [| (res_2 <> 0) |] 
  &&  [| (res_2 <= pcnt'_2) |] 
  &&  [| ((-res_2) <= pcnt'_2) |] 
  &&  [| ((make_prop2cnf_ret ((make_predata (clist') (pcnt') (ccnt'))) (res)) = (prop2cnf_logic (lt) ((make_predata (clist) (pcnt) (ccnt))))) |] 
  &&  [| (retval = res) |] 
  &&  [| (res <> 0) |] 
  &&  [| (res <= pcnt') |] 
  &&  [| ((-res) <= pcnt') |] 
  &&  [| ((prop_cnt_inf_SmtProp (lt)) <= pcnt) |] 
  &&  [| ((prop_cnt_inf_SmtProp (rt)) <= pcnt) |] 
  &&  [| (prop = (SmtB (op) (lt) (rt))) |] 
  &&  [| (p_pre <> 0) |] 
  &&  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t = 5) |]
  &&  (store_SmtProp z rt )
  **  (store_predata data_pre clist'_2 pcnt'_2 ccnt'_2 )
  **  (store_SmtProp y lt )
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "op")) # Int  |-> (SmtPBID (op)))
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop1")) # Ptr  |-> y)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop2")) # Ptr  |-> z)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
|--
  EX (clist'': (@list (@list Z)))  (pcnt'': Z)  (ccnt'': Z) ,
  [| ((make_prop2cnf_ret ((make_predata (clist'_2) (pcnt'_2) (ccnt'_2))) (res_2)) = (prop2cnf_logic (rt) ((make_predata (clist') (pcnt') (ccnt'))))) |] 
  &&  [| (retval_2 = res_2) |] 
  &&  [| (res_2 <> 0) |] 
  &&  [| (res_2 <= pcnt'_2) |] 
  &&  [| ((-res_2) <= pcnt'_2) |] 
  &&  [| ((make_prop2cnf_ret ((make_predata (clist') (pcnt') (ccnt'))) (res)) = (prop2cnf_logic (lt) ((make_predata (clist) (pcnt) (ccnt))))) |] 
  &&  [| (retval = res) |] 
  &&  [| (res <> 0) |] 
  &&  [| (res <= pcnt') |] 
  &&  [| ((-res) <= pcnt') |] 
  &&  [| ((prop_cnt_inf_SmtProp (lt)) <= pcnt) |] 
  &&  [| ((prop_cnt_inf_SmtProp (rt)) <= pcnt) |] 
  &&  [| (prop = (SmtB (op) (lt) (rt))) |] 
  &&  [| (p_pre <> 0) |] 
  &&  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t = 5) |]
  &&  (store_predata data_pre clist'' pcnt'' ccnt'' )
  **  (store_SmtProp z rt )
  **  (store_SmtProp y lt )
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "op")) # Int  |-> (SmtPBID (op)))
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop1")) # Ptr  |-> y)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop2")) # Ptr  |-> z)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
.

Definition prop2cnf_entail_wit_2 := 
forall (data_pre: Z) (p_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (prop: smt_prop) (t: Z) (y: Z) (op: SmtPropUop) (sub_prop: smt_prop) (clist': (@list (@list Z))) (pcnt': Z) (ccnt': Z) (res: Z) (retval: Z) ,
  [| ((make_prop2cnf_ret ((make_predata (clist') (pcnt') (ccnt'))) (res)) = (prop2cnf_logic (sub_prop) ((make_predata (clist) (pcnt) (ccnt))))) |] 
  &&  [| (retval = res) |] 
  &&  [| (res <> 0) |] 
  &&  [| (res <= pcnt') |] 
  &&  [| ((-res) <= pcnt') |] 
  &&  [| ((prop_cnt_inf_SmtProp (sub_prop)) <= pcnt) |] 
  &&  [| (prop = (SmtU (op) (sub_prop))) |] 
  &&  [| (p_pre <> 0) |] 
  &&  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t <> 5) |] 
  &&  [| (t = 6) |]
  &&  (store_SmtProp y sub_prop )
  **  (store_predata data_pre clist' pcnt' ccnt' )
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "op")) # Int  |-> (SmtPUID (op)))
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "prop1")) # Ptr  |-> y)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
|--
  EX (clist'': (@list (@list Z)))  (pcnt'': Z)  (ccnt'': Z) ,
  [| ((make_prop2cnf_ret ((make_predata (clist') (pcnt') (ccnt'))) (res)) = (prop2cnf_logic (sub_prop) ((make_predata (clist) (pcnt) (ccnt))))) |] 
  &&  [| (retval = res) |] 
  &&  [| (res <> 0) |] 
  &&  [| (res <= pcnt') |] 
  &&  [| ((-res) <= pcnt') |] 
  &&  [| ((prop_cnt_inf_SmtProp (sub_prop)) <= pcnt) |] 
  &&  [| (prop = (SmtU (op) (sub_prop))) |] 
  &&  [| (p_pre <> 0) |] 
  &&  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t <> 5) |] 
  &&  [| (t = 6) |]
  &&  (store_predata data_pre clist'' pcnt'' ccnt'' )
  **  (store_SmtProp y sub_prop )
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "op")) # Int  |-> (SmtPUID (op)))
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "prop1")) # Ptr  |-> y)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
.

Definition prop2cnf_return_wit_1_1 := 
forall (data_pre: Z) (p_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (prop: smt_prop) (t: Z) (var: Z) ,
  [| (prop = (SmtV (var))) |] 
  &&  [| (var <> 0) |] 
  &&  [| (p_pre <> 0) |] 
  &&  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t <> 5) |] 
  &&  [| (t <> 6) |] 
  &&  [| (t = 7) |]
  &&  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Propvar")) # Int  |-> var)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
  **  (store_predata data_pre clist pcnt ccnt )
|--
  EX (clist': (@list (@list Z)))  (pcnt': Z)  (ccnt': Z)  (res: Z) ,
  [| ((make_prop2cnf_ret ((make_predata (clist') (pcnt') (ccnt'))) (res)) = (prop2cnf_logic (prop) ((make_predata (clist) (pcnt) (ccnt))))) |] 
  &&  [| (var = res) |] 
  &&  [| (res <> 0) |] 
  &&  [| (res <= pcnt') |] 
  &&  [| ((-res) <= pcnt') |]
  &&  (store_SmtProp p_pre prop )
  **  (store_predata data_pre clist' pcnt' ccnt' )
.

Definition prop2cnf_return_wit_1_2 := 
forall (data_pre: Z) (p_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (prop: smt_prop) (t: Z) (y: Z) (op: SmtPropUop) (sub_prop: smt_prop) (clist'_2: (@list (@list Z))) (pcnt'_2: Z) (ccnt'_2: Z) (res_2: Z) (retval: Z) (clist'': (@list (@list Z))) (pcnt'': Z) (ccnt'': Z) ,
  [| (((prop_cnt_inf (clist'')) + 1 ) <= (pcnt'' + 1 )) |] 
  &&  [| ((pcnt'' + 1 ) <> 0) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist'')) = ccnt'') |] 
  &&  [| ((prop_cnt_inf (clist'')) <= pcnt'') |] 
  &&  [| (pcnt'' >= 0) |] 
  &&  [| ((make_prop2cnf_ret ((make_predata (clist'_2) (pcnt'_2) (ccnt'_2))) (res_2)) = (prop2cnf_logic (sub_prop) ((make_predata (clist) (pcnt) (ccnt))))) |] 
  &&  [| (retval = res_2) |] 
  &&  [| (res_2 <> 0) |] 
  &&  [| (res_2 <= pcnt'_2) |] 
  &&  [| ((-res_2) <= pcnt'_2) |] 
  &&  [| ((prop_cnt_inf_SmtProp (sub_prop)) <= pcnt) |] 
  &&  [| (prop = (SmtU (op) (sub_prop))) |] 
  &&  [| (p_pre <> 0) |] 
  &&  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t <> 5) |] 
  &&  [| (t = 6) |]
  &&  (store_predata data_pre (app ((iff2cnf_unary (retval) ((pcnt'' + 1 )))) (clist'')) (pcnt'' + 1 ) (ccnt'' + 2 ) )
  **  (store_SmtProp y sub_prop )
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "op")) # Int  |-> (SmtPUID (op)))
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "prop1")) # Ptr  |-> y)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
|--
  EX (clist': (@list (@list Z)))  (pcnt': Z)  (ccnt': Z)  (res: Z) ,
  [| ((make_prop2cnf_ret ((make_predata (clist') (pcnt') (ccnt'))) (res)) = (prop2cnf_logic (prop) ((make_predata (clist) (pcnt) (ccnt))))) |] 
  &&  [| ((pcnt'' + 1 ) = res) |] 
  &&  [| (res <> 0) |] 
  &&  [| (res <= pcnt') |] 
  &&  [| ((-res) <= pcnt') |]
  &&  (store_SmtProp p_pre prop )
  **  (store_predata data_pre clist' pcnt' ccnt' )
.

Definition prop2cnf_return_wit_1_3 := 
forall (data_pre: Z) (p_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (prop: smt_prop) (t: Z) (z: Z) (y: Z) (op: SmtPropBop) (lt: smt_prop) (rt: smt_prop) (clist'_2: (@list (@list Z))) (pcnt'_2: Z) (ccnt'_2: Z) (res_2: Z) (retval: Z) (clist'_3: (@list (@list Z))) (pcnt'_3: Z) (ccnt'_3: Z) (res_3: Z) (retval_2: Z) (clist'': (@list (@list Z))) (pcnt'': Z) (ccnt'': Z) ,
  [| (((prop_cnt_inf (clist'')) + 1 ) <= (pcnt'' + 1 )) |] 
  &&  [| ((pcnt'' + 1 ) <> 0) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist'')) = ccnt'') |] 
  &&  [| ((prop_cnt_inf (clist'')) <= pcnt'') |] 
  &&  [| (pcnt'' >= 0) |] 
  &&  [| ((make_prop2cnf_ret ((make_predata (clist'_3) (pcnt'_3) (ccnt'_3))) (res_3)) = (prop2cnf_logic (rt) ((make_predata (clist'_2) (pcnt'_2) (ccnt'_2))))) |] 
  &&  [| (retval_2 = res_3) |] 
  &&  [| (res_3 <> 0) |] 
  &&  [| (res_3 <= pcnt'_3) |] 
  &&  [| ((-res_3) <= pcnt'_3) |] 
  &&  [| ((make_prop2cnf_ret ((make_predata (clist'_2) (pcnt'_2) (ccnt'_2))) (res_2)) = (prop2cnf_logic (lt) ((make_predata (clist) (pcnt) (ccnt))))) |] 
  &&  [| (retval = res_2) |] 
  &&  [| (res_2 <> 0) |] 
  &&  [| (res_2 <= pcnt'_2) |] 
  &&  [| ((-res_2) <= pcnt'_2) |] 
  &&  [| ((prop_cnt_inf_SmtProp (lt)) <= pcnt) |] 
  &&  [| ((prop_cnt_inf_SmtProp (rt)) <= pcnt) |] 
  &&  [| (prop = (SmtB (op) (lt) (rt))) |] 
  &&  [| (p_pre <> 0) |] 
  &&  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t = 5) |]
  &&  (store_predata data_pre (app ((iff2cnf_binary (retval) (retval_2) ((pcnt'' + 1 )) (op))) (clist'')) (pcnt'' + 1 ) (ccnt'' + (iff2cnf_length_binary (retval) (retval_2) ((pcnt'' + 1 )) (op)) ) )
  **  (store_SmtProp z rt )
  **  (store_SmtProp y lt )
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "op")) # Int  |-> (SmtPBID (op)))
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop1")) # Ptr  |-> y)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop2")) # Ptr  |-> z)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
|--
  EX (clist': (@list (@list Z)))  (pcnt': Z)  (ccnt': Z)  (res: Z) ,
  [| ((make_prop2cnf_ret ((make_predata (clist') (pcnt') (ccnt'))) (res)) = (prop2cnf_logic (prop) ((make_predata (clist) (pcnt) (ccnt))))) |] 
  &&  [| ((pcnt'' + 1 ) = res) |] 
  &&  [| (res <> 0) |] 
  &&  [| (res <= pcnt') |] 
  &&  [| ((-res) <= pcnt') |]
  &&  (store_SmtProp p_pre prop )
  **  (store_predata data_pre clist' pcnt' ccnt' )
.

Definition prop2cnf_partial_solve_wit_1 := 
forall (data_pre: Z) (p_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (prop: smt_prop) ,
  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |]
  &&  (store_SmtProp p_pre prop )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |]
  &&  (store_SmtProp p_pre prop )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition prop2cnf_partial_solve_wit_2_pure := 
forall (data_pre: Z) (p_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (prop: smt_prop) (t: Z) ,
  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t = 5) |]
  &&  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> t)
  **  (store_SmtProp' p_pre prop )
  **  ((( &( "res" ) )) # Int  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| ((SmtPTID (prop)) = (SmtPTID (prop))) |] 
  &&  [| ((SmtPTID (prop)) = 5) |]
.

Definition prop2cnf_partial_solve_wit_2_aux := 
forall (data_pre: Z) (p_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (prop: smt_prop) (t: Z) ,
  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t = 5) |]
  &&  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> t)
  **  (store_SmtProp' p_pre prop )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| ((SmtPTID (prop)) = (SmtPTID (prop))) |] 
  &&  [| ((SmtPTID (prop)) = 5) |] 
  &&  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t = 5) |]
  &&  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
  **  (store_SmtProp' p_pre prop )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition prop2cnf_partial_solve_wit_2 := prop2cnf_partial_solve_wit_2_pure -> prop2cnf_partial_solve_wit_2_aux.

Definition prop2cnf_partial_solve_wit_3_pure := 
forall (data_pre: Z) (p_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (prop: smt_prop) (t: Z) (z: Z) (y: Z) (op: SmtPropBop) (lt: smt_prop) (rt: smt_prop) ,
  [| (prop = (SmtB (op) (lt) (rt))) |] 
  &&  [| (p_pre <> 0) |] 
  &&  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t = 5) |]
  &&  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "op")) # Int  |-> (SmtPBID (op)))
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop1")) # Ptr  |-> y)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop2")) # Ptr  |-> z)
  **  (store_SmtProp y lt )
  **  (store_SmtProp z rt )
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
  **  ((( &( "res" ) )) # Int  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |]
.

Definition prop2cnf_partial_solve_wit_3_aux := 
forall (data_pre: Z) (p_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (prop: smt_prop) (t: Z) (z: Z) (y: Z) (op: SmtPropBop) (lt: smt_prop) (rt: smt_prop) ,
  [| (prop = (SmtB (op) (lt) (rt))) |] 
  &&  [| (p_pre <> 0) |] 
  &&  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t = 5) |]
  &&  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "op")) # Int  |-> (SmtPBID (op)))
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop1")) # Ptr  |-> y)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop2")) # Ptr  |-> z)
  **  (store_SmtProp y lt )
  **  (store_SmtProp z rt )
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (prop = (SmtB (op) (lt) (rt))) |] 
  &&  [| (p_pre <> 0) |] 
  &&  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t = 5) |]
  &&  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "op")) # Int  |-> (SmtPBID (op)))
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop1")) # Ptr  |-> y)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop2")) # Ptr  |-> z)
  **  (store_SmtProp y lt )
  **  (store_SmtProp z rt )
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition prop2cnf_partial_solve_wit_3 := prop2cnf_partial_solve_wit_3_pure -> prop2cnf_partial_solve_wit_3_aux.

Definition prop2cnf_partial_solve_wit_4_pure := 
forall (data_pre: Z) (p_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (prop: smt_prop) (t: Z) (z: Z) (y: Z) (op: SmtPropBop) (lt: smt_prop) (rt: smt_prop) ,
  [| ((prop_cnt_inf_SmtProp (lt)) <= pcnt) |] 
  &&  [| ((prop_cnt_inf_SmtProp (rt)) <= pcnt) |] 
  &&  [| (prop = (SmtB (op) (lt) (rt))) |] 
  &&  [| (p_pre <> 0) |] 
  &&  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t = 5) |]
  &&  ((( &( "p1" ) )) # Int  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "op")) # Int  |-> (SmtPBID (op)))
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop1")) # Ptr  |-> y)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop2")) # Ptr  |-> z)
  **  (store_SmtProp y lt )
  **  (store_SmtProp z rt )
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
  **  ((( &( "res" ) )) # Int  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| ((prop_cnt_inf_SmtProp (lt)) <= pcnt) |]
.

Definition prop2cnf_partial_solve_wit_4_aux := 
forall (data_pre: Z) (p_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (prop: smt_prop) (t: Z) (z: Z) (y: Z) (op: SmtPropBop) (lt: smt_prop) (rt: smt_prop) ,
  [| ((prop_cnt_inf_SmtProp (lt)) <= pcnt) |] 
  &&  [| ((prop_cnt_inf_SmtProp (rt)) <= pcnt) |] 
  &&  [| (prop = (SmtB (op) (lt) (rt))) |] 
  &&  [| (p_pre <> 0) |] 
  &&  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t = 5) |]
  &&  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "op")) # Int  |-> (SmtPBID (op)))
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop1")) # Ptr  |-> y)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop2")) # Ptr  |-> z)
  **  (store_SmtProp y lt )
  **  (store_SmtProp z rt )
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| ((prop_cnt_inf_SmtProp (lt)) <= pcnt) |] 
  &&  [| ((prop_cnt_inf_SmtProp (lt)) <= pcnt) |] 
  &&  [| ((prop_cnt_inf_SmtProp (rt)) <= pcnt) |] 
  &&  [| (prop = (SmtB (op) (lt) (rt))) |] 
  &&  [| (p_pre <> 0) |] 
  &&  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t = 5) |]
  &&  (store_SmtProp y lt )
  **  (store_predata data_pre clist pcnt ccnt )
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "op")) # Int  |-> (SmtPBID (op)))
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop1")) # Ptr  |-> y)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop2")) # Ptr  |-> z)
  **  (store_SmtProp z rt )
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
.

Definition prop2cnf_partial_solve_wit_4 := prop2cnf_partial_solve_wit_4_pure -> prop2cnf_partial_solve_wit_4_aux.

Definition prop2cnf_partial_solve_wit_5_pure := 
forall (data_pre: Z) (p_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (prop: smt_prop) (t: Z) (z: Z) (y: Z) (op: SmtPropBop) (lt: smt_prop) (rt: smt_prop) (clist': (@list (@list Z))) (pcnt': Z) (ccnt': Z) (res: Z) (retval: Z) ,
  [| ((make_prop2cnf_ret ((make_predata (clist') (pcnt') (ccnt'))) (res)) = (prop2cnf_logic (lt) ((make_predata (clist) (pcnt) (ccnt))))) |] 
  &&  [| (retval = res) |] 
  &&  [| (res <> 0) |] 
  &&  [| (res <= pcnt') |] 
  &&  [| ((-res) <= pcnt') |] 
  &&  [| ((prop_cnt_inf_SmtProp (lt)) <= pcnt) |] 
  &&  [| ((prop_cnt_inf_SmtProp (rt)) <= pcnt) |] 
  &&  [| (prop = (SmtB (op) (lt) (rt))) |] 
  &&  [| (p_pre <> 0) |] 
  &&  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t = 5) |]
  &&  ((( &( "p2" ) )) # Int  |->_)
  **  (store_SmtProp y lt )
  **  (store_predata data_pre clist' pcnt' ccnt' )
  **  ((( &( "p1" ) )) # Int  |-> retval)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "op")) # Int  |-> (SmtPBID (op)))
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop1")) # Ptr  |-> y)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop2")) # Ptr  |-> z)
  **  (store_SmtProp z rt )
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
  **  ((( &( "res" ) )) # Int  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
|--
  [| ((prop_cnt_inf_SmtProp (rt)) <= pcnt') |]
.

Definition prop2cnf_partial_solve_wit_5_aux := 
forall (data_pre: Z) (p_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (prop: smt_prop) (t: Z) (z: Z) (y: Z) (op: SmtPropBop) (lt: smt_prop) (rt: smt_prop) (clist': (@list (@list Z))) (pcnt': Z) (ccnt': Z) (res: Z) (retval: Z) ,
  [| ((make_prop2cnf_ret ((make_predata (clist') (pcnt') (ccnt'))) (res)) = (prop2cnf_logic (lt) ((make_predata (clist) (pcnt) (ccnt))))) |] 
  &&  [| (retval = res) |] 
  &&  [| (res <> 0) |] 
  &&  [| (res <= pcnt') |] 
  &&  [| ((-res) <= pcnt') |] 
  &&  [| ((prop_cnt_inf_SmtProp (lt)) <= pcnt) |] 
  &&  [| ((prop_cnt_inf_SmtProp (rt)) <= pcnt) |] 
  &&  [| (prop = (SmtB (op) (lt) (rt))) |] 
  &&  [| (p_pre <> 0) |] 
  &&  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t = 5) |]
  &&  (store_SmtProp y lt )
  **  (store_predata data_pre clist' pcnt' ccnt' )
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "op")) # Int  |-> (SmtPBID (op)))
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop1")) # Ptr  |-> y)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop2")) # Ptr  |-> z)
  **  (store_SmtProp z rt )
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
|--
  [| ((prop_cnt_inf_SmtProp (rt)) <= pcnt') |] 
  &&  [| ((make_prop2cnf_ret ((make_predata (clist') (pcnt') (ccnt'))) (res)) = (prop2cnf_logic (lt) ((make_predata (clist) (pcnt) (ccnt))))) |] 
  &&  [| (retval = res) |] 
  &&  [| (res <> 0) |] 
  &&  [| (res <= pcnt') |] 
  &&  [| ((-res) <= pcnt') |] 
  &&  [| ((prop_cnt_inf_SmtProp (lt)) <= pcnt) |] 
  &&  [| ((prop_cnt_inf_SmtProp (rt)) <= pcnt) |] 
  &&  [| (prop = (SmtB (op) (lt) (rt))) |] 
  &&  [| (p_pre <> 0) |] 
  &&  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t = 5) |]
  &&  (store_SmtProp z rt )
  **  (store_predata data_pre clist' pcnt' ccnt' )
  **  (store_SmtProp y lt )
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "op")) # Int  |-> (SmtPBID (op)))
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop1")) # Ptr  |-> y)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop2")) # Ptr  |-> z)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
.

Definition prop2cnf_partial_solve_wit_5 := prop2cnf_partial_solve_wit_5_pure -> prop2cnf_partial_solve_wit_5_aux.

Definition prop2cnf_partial_solve_wit_6 := 
forall (data_pre: Z) (p_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (prop: smt_prop) (t: Z) (z: Z) (y: Z) (op: SmtPropBop) (lt: smt_prop) (rt: smt_prop) (clist': (@list (@list Z))) (pcnt': Z) (ccnt': Z) (res: Z) (retval: Z) (clist'_2: (@list (@list Z))) (pcnt'_2: Z) (ccnt'_2: Z) (res_2: Z) (retval_2: Z) (clist'': (@list (@list Z))) (pcnt'': Z) (ccnt'': Z) ,
  [| ((make_prop2cnf_ret ((make_predata (clist'_2) (pcnt'_2) (ccnt'_2))) (res_2)) = (prop2cnf_logic (rt) ((make_predata (clist') (pcnt') (ccnt'))))) |] 
  &&  [| (retval_2 = res_2) |] 
  &&  [| (res_2 <> 0) |] 
  &&  [| (res_2 <= pcnt'_2) |] 
  &&  [| ((-res_2) <= pcnt'_2) |] 
  &&  [| ((make_prop2cnf_ret ((make_predata (clist') (pcnt') (ccnt'))) (res)) = (prop2cnf_logic (lt) ((make_predata (clist) (pcnt) (ccnt))))) |] 
  &&  [| (retval = res) |] 
  &&  [| (res <> 0) |] 
  &&  [| (res <= pcnt') |] 
  &&  [| ((-res) <= pcnt') |] 
  &&  [| ((prop_cnt_inf_SmtProp (lt)) <= pcnt) |] 
  &&  [| ((prop_cnt_inf_SmtProp (rt)) <= pcnt) |] 
  &&  [| (prop = (SmtB (op) (lt) (rt))) |] 
  &&  [| (p_pre <> 0) |] 
  &&  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t = 5) |]
  &&  (store_predata data_pre clist'' pcnt'' ccnt'' )
  **  (store_SmtProp z rt )
  **  (store_SmtProp y lt )
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "op")) # Int  |-> (SmtPBID (op)))
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop1")) # Ptr  |-> y)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop2")) # Ptr  |-> z)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
|--
  [| ((make_prop2cnf_ret ((make_predata (clist'_2) (pcnt'_2) (ccnt'_2))) (res_2)) = (prop2cnf_logic (rt) ((make_predata (clist') (pcnt') (ccnt'))))) |] 
  &&  [| (retval_2 = res_2) |] 
  &&  [| (res_2 <> 0) |] 
  &&  [| (res_2 <= pcnt'_2) |] 
  &&  [| ((-res_2) <= pcnt'_2) |] 
  &&  [| ((make_prop2cnf_ret ((make_predata (clist') (pcnt') (ccnt'))) (res)) = (prop2cnf_logic (lt) ((make_predata (clist) (pcnt) (ccnt))))) |] 
  &&  [| (retval = res) |] 
  &&  [| (res <> 0) |] 
  &&  [| (res <= pcnt') |] 
  &&  [| ((-res) <= pcnt') |] 
  &&  [| ((prop_cnt_inf_SmtProp (lt)) <= pcnt) |] 
  &&  [| ((prop_cnt_inf_SmtProp (rt)) <= pcnt) |] 
  &&  [| (prop = (SmtB (op) (lt) (rt))) |] 
  &&  [| (p_pre <> 0) |] 
  &&  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t = 5) |]
  &&  (store_predata data_pre clist'' pcnt'' ccnt'' )
  **  (store_SmtProp z rt )
  **  (store_SmtProp y lt )
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "op")) # Int  |-> (SmtPBID (op)))
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop1")) # Ptr  |-> y)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop2")) # Ptr  |-> z)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
.

Definition prop2cnf_partial_solve_wit_7_pure := 
forall (data_pre: Z) (p_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (prop: smt_prop) (t: Z) (z: Z) (y: Z) (op: SmtPropBop) (lt: smt_prop) (rt: smt_prop) (clist': (@list (@list Z))) (pcnt': Z) (ccnt': Z) (res: Z) (retval: Z) (clist'_2: (@list (@list Z))) (pcnt'_2: Z) (ccnt'_2: Z) (res_2: Z) (retval_2: Z) (clist'': (@list (@list Z))) (pcnt'': Z) (ccnt'': Z) (y'': Z) ,
  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist'')) = ccnt'') |] 
  &&  [| ((prop_cnt_inf (clist'')) <= pcnt'') |] 
  &&  [| (pcnt'' >= 0) |] 
  &&  [| ((make_prop2cnf_ret ((make_predata (clist'_2) (pcnt'_2) (ccnt'_2))) (res_2)) = (prop2cnf_logic (rt) ((make_predata (clist') (pcnt') (ccnt'))))) |] 
  &&  [| (retval_2 = res_2) |] 
  &&  [| (res_2 <> 0) |] 
  &&  [| (res_2 <= pcnt'_2) |] 
  &&  [| ((-res_2) <= pcnt'_2) |] 
  &&  [| ((make_prop2cnf_ret ((make_predata (clist') (pcnt') (ccnt'))) (res)) = (prop2cnf_logic (lt) ((make_predata (clist) (pcnt) (ccnt))))) |] 
  &&  [| (retval = res) |] 
  &&  [| (res <> 0) |] 
  &&  [| (res <= pcnt') |] 
  &&  [| ((-res) <= pcnt') |] 
  &&  [| ((prop_cnt_inf_SmtProp (lt)) <= pcnt) |] 
  &&  [| ((prop_cnt_inf_SmtProp (rt)) <= pcnt) |] 
  &&  [| (prop = (SmtB (op) (lt) (rt))) |] 
  &&  [| (p_pre <> 0) |] 
  &&  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t = 5) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y'')
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> (pcnt'' + 1 ))
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt'')
  **  (sll_cnf_list y'' clist'' )
  **  (store_SmtProp z rt )
  **  ((( &( "p2" ) )) # Int  |-> retval_2)
  **  (store_SmtProp y lt )
  **  ((( &( "p1" ) )) # Int  |-> retval)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "op")) # Int  |-> (SmtPBID (op)))
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop1")) # Ptr  |-> y)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop2")) # Ptr  |-> z)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
  **  ((( &( "res" ) )) # Int  |-> (pcnt'' + 1 ))
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
|--
  [| (pcnt'' >= 0) |] 
  &&  [| ((pcnt'' + 1 ) = (pcnt'' + 1 )) |]
.

Definition prop2cnf_partial_solve_wit_7_aux := 
forall (data_pre: Z) (p_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (prop: smt_prop) (t: Z) (z: Z) (y: Z) (op: SmtPropBop) (lt: smt_prop) (rt: smt_prop) (clist': (@list (@list Z))) (pcnt': Z) (ccnt': Z) (res: Z) (retval: Z) (clist'_2: (@list (@list Z))) (pcnt'_2: Z) (ccnt'_2: Z) (res_2: Z) (retval_2: Z) (clist'': (@list (@list Z))) (pcnt'': Z) (ccnt'': Z) (y'': Z) ,
  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist'')) = ccnt'') |] 
  &&  [| ((prop_cnt_inf (clist'')) <= pcnt'') |] 
  &&  [| (pcnt'' >= 0) |] 
  &&  [| ((make_prop2cnf_ret ((make_predata (clist'_2) (pcnt'_2) (ccnt'_2))) (res_2)) = (prop2cnf_logic (rt) ((make_predata (clist') (pcnt') (ccnt'))))) |] 
  &&  [| (retval_2 = res_2) |] 
  &&  [| (res_2 <> 0) |] 
  &&  [| (res_2 <= pcnt'_2) |] 
  &&  [| ((-res_2) <= pcnt'_2) |] 
  &&  [| ((make_prop2cnf_ret ((make_predata (clist') (pcnt') (ccnt'))) (res)) = (prop2cnf_logic (lt) ((make_predata (clist) (pcnt) (ccnt))))) |] 
  &&  [| (retval = res) |] 
  &&  [| (res <> 0) |] 
  &&  [| (res <= pcnt') |] 
  &&  [| ((-res) <= pcnt') |] 
  &&  [| ((prop_cnt_inf_SmtProp (lt)) <= pcnt) |] 
  &&  [| ((prop_cnt_inf_SmtProp (rt)) <= pcnt) |] 
  &&  [| (prop = (SmtB (op) (lt) (rt))) |] 
  &&  [| (p_pre <> 0) |] 
  &&  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t = 5) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y'')
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> (pcnt'' + 1 ))
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt'')
  **  (sll_cnf_list y'' clist'' )
  **  (store_SmtProp z rt )
  **  (store_SmtProp y lt )
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "op")) # Int  |-> (SmtPBID (op)))
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop1")) # Ptr  |-> y)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop2")) # Ptr  |-> z)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
|--
  [| (pcnt'' >= 0) |] 
  &&  [| ((pcnt'' + 1 ) = (pcnt'' + 1 )) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist'')) = ccnt'') |] 
  &&  [| ((prop_cnt_inf (clist'')) <= pcnt'') |] 
  &&  [| (pcnt'' >= 0) |] 
  &&  [| ((make_prop2cnf_ret ((make_predata (clist'_2) (pcnt'_2) (ccnt'_2))) (res_2)) = (prop2cnf_logic (rt) ((make_predata (clist') (pcnt') (ccnt'))))) |] 
  &&  [| (retval_2 = res_2) |] 
  &&  [| (res_2 <> 0) |] 
  &&  [| (res_2 <= pcnt'_2) |] 
  &&  [| ((-res_2) <= pcnt'_2) |] 
  &&  [| ((make_prop2cnf_ret ((make_predata (clist') (pcnt') (ccnt'))) (res)) = (prop2cnf_logic (lt) ((make_predata (clist) (pcnt) (ccnt))))) |] 
  &&  [| (retval = res) |] 
  &&  [| (res <> 0) |] 
  &&  [| (res <= pcnt') |] 
  &&  [| ((-res) <= pcnt') |] 
  &&  [| ((prop_cnt_inf_SmtProp (lt)) <= pcnt) |] 
  &&  [| ((prop_cnt_inf_SmtProp (rt)) <= pcnt) |] 
  &&  [| (prop = (SmtB (op) (lt) (rt))) |] 
  &&  [| (p_pre <> 0) |] 
  &&  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t = 5) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y'')
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> (pcnt'' + 1 ))
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt'')
  **  (sll_cnf_list y'' clist'' )
  **  (store_SmtProp z rt )
  **  (store_SmtProp y lt )
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "op")) # Int  |-> (SmtPBID (op)))
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop1")) # Ptr  |-> y)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop2")) # Ptr  |-> z)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
.

Definition prop2cnf_partial_solve_wit_7 := prop2cnf_partial_solve_wit_7_pure -> prop2cnf_partial_solve_wit_7_aux.

Definition prop2cnf_partial_solve_wit_8_pure := 
forall (data_pre: Z) (p_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (prop: smt_prop) (t: Z) (z: Z) (y: Z) (op: SmtPropBop) (lt: smt_prop) (rt: smt_prop) (clist': (@list (@list Z))) (pcnt': Z) (ccnt': Z) (res: Z) (retval: Z) (clist'_2: (@list (@list Z))) (pcnt'_2: Z) (ccnt'_2: Z) (res_2: Z) (retval_2: Z) (clist'': (@list (@list Z))) (pcnt'': Z) (ccnt'': Z) (y'': Z) ,
  [| ((pcnt'' + 1 ) <> 0) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist'')) = ccnt'') |] 
  &&  [| ((prop_cnt_inf (clist'')) <= pcnt'') |] 
  &&  [| (pcnt'' >= 0) |] 
  &&  [| ((make_prop2cnf_ret ((make_predata (clist'_2) (pcnt'_2) (ccnt'_2))) (res_2)) = (prop2cnf_logic (rt) ((make_predata (clist') (pcnt') (ccnt'))))) |] 
  &&  [| (retval_2 = res_2) |] 
  &&  [| (res_2 <> 0) |] 
  &&  [| (res_2 <= pcnt'_2) |] 
  &&  [| ((-res_2) <= pcnt'_2) |] 
  &&  [| ((make_prop2cnf_ret ((make_predata (clist') (pcnt') (ccnt'))) (res)) = (prop2cnf_logic (lt) ((make_predata (clist) (pcnt) (ccnt))))) |] 
  &&  [| (retval = res) |] 
  &&  [| (res <> 0) |] 
  &&  [| (res <= pcnt') |] 
  &&  [| ((-res) <= pcnt') |] 
  &&  [| ((prop_cnt_inf_SmtProp (lt)) <= pcnt) |] 
  &&  [| ((prop_cnt_inf_SmtProp (rt)) <= pcnt) |] 
  &&  [| (prop = (SmtB (op) (lt) (rt))) |] 
  &&  [| (p_pre <> 0) |] 
  &&  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t = 5) |]
  &&  ((( &( "res" ) )) # Int  |-> (pcnt'' + 1 ))
  **  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y'')
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> (pcnt'' + 1 ))
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt'')
  **  (sll_cnf_list y'' clist'' )
  **  (store_SmtProp z rt )
  **  ((( &( "p2" ) )) # Int  |-> retval_2)
  **  (store_SmtProp y lt )
  **  ((( &( "p1" ) )) # Int  |-> retval)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "op")) # Int  |-> (SmtPBID (op)))
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop1")) # Ptr  |-> y)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop2")) # Ptr  |-> z)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
|--
  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist'')) = ccnt'') |] 
  &&  [| ((prop_cnt_inf (clist'')) <= pcnt'') |]
.

Definition prop2cnf_partial_solve_wit_8_aux := 
forall (data_pre: Z) (p_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (prop: smt_prop) (t: Z) (z: Z) (y: Z) (op: SmtPropBop) (lt: smt_prop) (rt: smt_prop) (clist': (@list (@list Z))) (pcnt': Z) (ccnt': Z) (res: Z) (retval: Z) (clist'_2: (@list (@list Z))) (pcnt'_2: Z) (ccnt'_2: Z) (res_2: Z) (retval_2: Z) (clist'': (@list (@list Z))) (pcnt'': Z) (ccnt'': Z) (y'': Z) ,
  [| ((pcnt'' + 1 ) <> 0) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist'')) = ccnt'') |] 
  &&  [| ((prop_cnt_inf (clist'')) <= pcnt'') |] 
  &&  [| (pcnt'' >= 0) |] 
  &&  [| ((make_prop2cnf_ret ((make_predata (clist'_2) (pcnt'_2) (ccnt'_2))) (res_2)) = (prop2cnf_logic (rt) ((make_predata (clist') (pcnt') (ccnt'))))) |] 
  &&  [| (retval_2 = res_2) |] 
  &&  [| (res_2 <> 0) |] 
  &&  [| (res_2 <= pcnt'_2) |] 
  &&  [| ((-res_2) <= pcnt'_2) |] 
  &&  [| ((make_prop2cnf_ret ((make_predata (clist') (pcnt') (ccnt'))) (res)) = (prop2cnf_logic (lt) ((make_predata (clist) (pcnt) (ccnt))))) |] 
  &&  [| (retval = res) |] 
  &&  [| (res <> 0) |] 
  &&  [| (res <= pcnt') |] 
  &&  [| ((-res) <= pcnt') |] 
  &&  [| ((prop_cnt_inf_SmtProp (lt)) <= pcnt) |] 
  &&  [| ((prop_cnt_inf_SmtProp (rt)) <= pcnt) |] 
  &&  [| (prop = (SmtB (op) (lt) (rt))) |] 
  &&  [| (p_pre <> 0) |] 
  &&  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t = 5) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y'')
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> (pcnt'' + 1 ))
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt'')
  **  (sll_cnf_list y'' clist'' )
  **  (store_SmtProp z rt )
  **  (store_SmtProp y lt )
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "op")) # Int  |-> (SmtPBID (op)))
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop1")) # Ptr  |-> y)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop2")) # Ptr  |-> z)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
|--
  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist'')) = ccnt'') |] 
  &&  [| ((prop_cnt_inf (clist'')) <= pcnt'') |] 
  &&  [| ((pcnt'' + 1 ) <> 0) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist'')) = ccnt'') |] 
  &&  [| ((prop_cnt_inf (clist'')) <= pcnt'') |] 
  &&  [| (pcnt'' >= 0) |] 
  &&  [| ((make_prop2cnf_ret ((make_predata (clist'_2) (pcnt'_2) (ccnt'_2))) (res_2)) = (prop2cnf_logic (rt) ((make_predata (clist') (pcnt') (ccnt'))))) |] 
  &&  [| (retval_2 = res_2) |] 
  &&  [| (res_2 <> 0) |] 
  &&  [| (res_2 <= pcnt'_2) |] 
  &&  [| ((-res_2) <= pcnt'_2) |] 
  &&  [| ((make_prop2cnf_ret ((make_predata (clist') (pcnt') (ccnt'))) (res)) = (prop2cnf_logic (lt) ((make_predata (clist) (pcnt) (ccnt))))) |] 
  &&  [| (retval = res) |] 
  &&  [| (res <> 0) |] 
  &&  [| (res <= pcnt') |] 
  &&  [| ((-res) <= pcnt') |] 
  &&  [| ((prop_cnt_inf_SmtProp (lt)) <= pcnt) |] 
  &&  [| ((prop_cnt_inf_SmtProp (rt)) <= pcnt) |] 
  &&  [| (prop = (SmtB (op) (lt) (rt))) |] 
  &&  [| (p_pre <> 0) |] 
  &&  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t = 5) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y'')
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> (pcnt'' + 1 ))
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt'')
  **  (sll_cnf_list y'' clist'' )
  **  (store_SmtProp z rt )
  **  (store_SmtProp y lt )
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "op")) # Int  |-> (SmtPBID (op)))
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop1")) # Ptr  |-> y)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop2")) # Ptr  |-> z)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
.

Definition prop2cnf_partial_solve_wit_8 := prop2cnf_partial_solve_wit_8_pure -> prop2cnf_partial_solve_wit_8_aux.

Definition prop2cnf_partial_solve_wit_9_pure := 
forall (data_pre: Z) (p_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (prop: smt_prop) (t: Z) (z: Z) (y: Z) (op: SmtPropBop) (lt: smt_prop) (rt: smt_prop) (clist': (@list (@list Z))) (pcnt': Z) (ccnt': Z) (res: Z) (retval: Z) (clist'_2: (@list (@list Z))) (pcnt'_2: Z) (ccnt'_2: Z) (res_2: Z) (retval_2: Z) (clist'': (@list (@list Z))) (pcnt'': Z) (ccnt'': Z) ,
  [| ((pcnt'' + 1 ) <> 0) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist'')) = ccnt'') |] 
  &&  [| ((prop_cnt_inf (clist'')) <= pcnt'') |] 
  &&  [| (pcnt'' >= 0) |] 
  &&  [| ((make_prop2cnf_ret ((make_predata (clist'_2) (pcnt'_2) (ccnt'_2))) (res_2)) = (prop2cnf_logic (rt) ((make_predata (clist') (pcnt') (ccnt'))))) |] 
  &&  [| (retval_2 = res_2) |] 
  &&  [| (res_2 <> 0) |] 
  &&  [| (res_2 <= pcnt'_2) |] 
  &&  [| ((-res_2) <= pcnt'_2) |] 
  &&  [| ((make_prop2cnf_ret ((make_predata (clist') (pcnt') (ccnt'))) (res)) = (prop2cnf_logic (lt) ((make_predata (clist) (pcnt) (ccnt))))) |] 
  &&  [| (retval = res) |] 
  &&  [| (res <> 0) |] 
  &&  [| (res <= pcnt') |] 
  &&  [| ((-res) <= pcnt') |] 
  &&  [| ((prop_cnt_inf_SmtProp (lt)) <= pcnt) |] 
  &&  [| ((prop_cnt_inf_SmtProp (rt)) <= pcnt) |] 
  &&  [| (prop = (SmtB (op) (lt) (rt))) |] 
  &&  [| (p_pre <> 0) |] 
  &&  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t = 5) |]
  &&  (store_predata data_pre clist'' (pcnt'' + 1 ) ccnt'' )
  **  ((( &( "res" ) )) # Int  |-> (pcnt'' + 1 ))
  **  (store_SmtProp z rt )
  **  ((( &( "p2" ) )) # Int  |-> retval_2)
  **  (store_SmtProp y lt )
  **  ((( &( "p1" ) )) # Int  |-> retval)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "op")) # Int  |-> (SmtPBID (op)))
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop1")) # Ptr  |-> y)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop2")) # Ptr  |-> z)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
|--
  [| ((prop_cnt_inf (clist'')) <= pcnt'') |]
.

Definition prop2cnf_partial_solve_wit_9_aux := 
forall (data_pre: Z) (p_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (prop: smt_prop) (t: Z) (z: Z) (y: Z) (op: SmtPropBop) (lt: smt_prop) (rt: smt_prop) (clist': (@list (@list Z))) (pcnt': Z) (ccnt': Z) (res: Z) (retval: Z) (clist'_2: (@list (@list Z))) (pcnt'_2: Z) (ccnt'_2: Z) (res_2: Z) (retval_2: Z) (clist'': (@list (@list Z))) (pcnt'': Z) (ccnt'': Z) ,
  [| ((pcnt'' + 1 ) <> 0) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist'')) = ccnt'') |] 
  &&  [| ((prop_cnt_inf (clist'')) <= pcnt'') |] 
  &&  [| (pcnt'' >= 0) |] 
  &&  [| ((make_prop2cnf_ret ((make_predata (clist'_2) (pcnt'_2) (ccnt'_2))) (res_2)) = (prop2cnf_logic (rt) ((make_predata (clist') (pcnt') (ccnt'))))) |] 
  &&  [| (retval_2 = res_2) |] 
  &&  [| (res_2 <> 0) |] 
  &&  [| (res_2 <= pcnt'_2) |] 
  &&  [| ((-res_2) <= pcnt'_2) |] 
  &&  [| ((make_prop2cnf_ret ((make_predata (clist') (pcnt') (ccnt'))) (res)) = (prop2cnf_logic (lt) ((make_predata (clist) (pcnt) (ccnt))))) |] 
  &&  [| (retval = res) |] 
  &&  [| (res <> 0) |] 
  &&  [| (res <= pcnt') |] 
  &&  [| ((-res) <= pcnt') |] 
  &&  [| ((prop_cnt_inf_SmtProp (lt)) <= pcnt) |] 
  &&  [| ((prop_cnt_inf_SmtProp (rt)) <= pcnt) |] 
  &&  [| (prop = (SmtB (op) (lt) (rt))) |] 
  &&  [| (p_pre <> 0) |] 
  &&  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t = 5) |]
  &&  (store_predata data_pre clist'' (pcnt'' + 1 ) ccnt'' )
  **  (store_SmtProp z rt )
  **  (store_SmtProp y lt )
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "op")) # Int  |-> (SmtPBID (op)))
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop1")) # Ptr  |-> y)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop2")) # Ptr  |-> z)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
|--
  [| ((prop_cnt_inf (clist'')) <= pcnt'') |] 
  &&  [| ((pcnt'' + 1 ) <> 0) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist'')) = ccnt'') |] 
  &&  [| ((prop_cnt_inf (clist'')) <= pcnt'') |] 
  &&  [| (pcnt'' >= 0) |] 
  &&  [| ((make_prop2cnf_ret ((make_predata (clist'_2) (pcnt'_2) (ccnt'_2))) (res_2)) = (prop2cnf_logic (rt) ((make_predata (clist') (pcnt') (ccnt'))))) |] 
  &&  [| (retval_2 = res_2) |] 
  &&  [| (res_2 <> 0) |] 
  &&  [| (res_2 <= pcnt'_2) |] 
  &&  [| ((-res_2) <= pcnt'_2) |] 
  &&  [| ((make_prop2cnf_ret ((make_predata (clist') (pcnt') (ccnt'))) (res)) = (prop2cnf_logic (lt) ((make_predata (clist) (pcnt) (ccnt))))) |] 
  &&  [| (retval = res) |] 
  &&  [| (res <> 0) |] 
  &&  [| (res <= pcnt') |] 
  &&  [| ((-res) <= pcnt') |] 
  &&  [| ((prop_cnt_inf_SmtProp (lt)) <= pcnt) |] 
  &&  [| ((prop_cnt_inf_SmtProp (rt)) <= pcnt) |] 
  &&  [| (prop = (SmtB (op) (lt) (rt))) |] 
  &&  [| (p_pre <> 0) |] 
  &&  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t = 5) |]
  &&  (store_predata data_pre clist'' (pcnt'' + 1 ) ccnt'' )
  **  (store_SmtProp z rt )
  **  (store_SmtProp y lt )
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "op")) # Int  |-> (SmtPBID (op)))
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop1")) # Ptr  |-> y)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop2")) # Ptr  |-> z)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
.

Definition prop2cnf_partial_solve_wit_9 := prop2cnf_partial_solve_wit_9_pure -> prop2cnf_partial_solve_wit_9_aux.

Definition prop2cnf_partial_solve_wit_10_pure := 
forall (data_pre: Z) (p_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (prop: smt_prop) (t: Z) (z: Z) (y: Z) (op: SmtPropBop) (lt: smt_prop) (rt: smt_prop) (clist': (@list (@list Z))) (pcnt': Z) (ccnt': Z) (res: Z) (retval: Z) (clist'_2: (@list (@list Z))) (pcnt'_2: Z) (ccnt'_2: Z) (res_2: Z) (retval_2: Z) (clist'': (@list (@list Z))) (pcnt'': Z) (ccnt'': Z) ,
  [| (((prop_cnt_inf (clist'')) + 1 ) <= (pcnt'' + 1 )) |] 
  &&  [| ((pcnt'' + 1 ) <> 0) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist'')) = ccnt'') |] 
  &&  [| ((prop_cnt_inf (clist'')) <= pcnt'') |] 
  &&  [| (pcnt'' >= 0) |] 
  &&  [| ((make_prop2cnf_ret ((make_predata (clist'_2) (pcnt'_2) (ccnt'_2))) (res_2)) = (prop2cnf_logic (rt) ((make_predata (clist') (pcnt') (ccnt'))))) |] 
  &&  [| (retval_2 = res_2) |] 
  &&  [| (res_2 <> 0) |] 
  &&  [| (res_2 <= pcnt'_2) |] 
  &&  [| ((-res_2) <= pcnt'_2) |] 
  &&  [| ((make_prop2cnf_ret ((make_predata (clist') (pcnt') (ccnt'))) (res)) = (prop2cnf_logic (lt) ((make_predata (clist) (pcnt) (ccnt))))) |] 
  &&  [| (retval = res) |] 
  &&  [| (res <> 0) |] 
  &&  [| (res <= pcnt') |] 
  &&  [| ((-res) <= pcnt') |] 
  &&  [| ((prop_cnt_inf_SmtProp (lt)) <= pcnt) |] 
  &&  [| ((prop_cnt_inf_SmtProp (rt)) <= pcnt) |] 
  &&  [| (prop = (SmtB (op) (lt) (rt))) |] 
  &&  [| (p_pre <> 0) |] 
  &&  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t = 5) |]
  &&  (store_predata data_pre clist'' (pcnt'' + 1 ) ccnt'' )
  **  ((( &( "res" ) )) # Int  |-> (pcnt'' + 1 ))
  **  (store_SmtProp z rt )
  **  ((( &( "p2" ) )) # Int  |-> retval_2)
  **  (store_SmtProp y lt )
  **  ((( &( "p1" ) )) # Int  |-> retval)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "op")) # Int  |-> (SmtPBID (op)))
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop1")) # Ptr  |-> y)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop2")) # Ptr  |-> z)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
|--
  [| (retval <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| ((pcnt'' + 1 ) <> 0) |] 
  &&  [| (retval <= (pcnt'' + 1 )) |] 
  &&  [| (retval_2 <= (pcnt'' + 1 )) |] 
  &&  [| ((pcnt'' + 1 ) <= (pcnt'' + 1 )) |] 
  &&  [| ((-retval) <= (pcnt'' + 1 )) |] 
  &&  [| ((-retval_2) <= (pcnt'' + 1 )) |] 
  &&  [| ((-(pcnt'' + 1 )) <= (pcnt'' + 1 )) |] 
  &&  [| (((prop_cnt_inf (clist'')) + 1 ) <= (pcnt'' + 1 )) |] 
  &&  [| ((SmtPBID (op)) = (SmtPBID (op))) |] 
  &&  [| ((-res_2) <= (pcnt'' + 1 )) |] 
  &&  [| ((-res) <= (pcnt'' + 1 )) |] 
  &&  [| (res_2 <= (pcnt'' + 1 )) |] 
  &&  [| (res <= (pcnt'' + 1 )) |]
.

Definition prop2cnf_partial_solve_wit_10_aux := 
forall (data_pre: Z) (p_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (prop: smt_prop) (t: Z) (z: Z) (y: Z) (op: SmtPropBop) (lt: smt_prop) (rt: smt_prop) (clist': (@list (@list Z))) (pcnt': Z) (ccnt': Z) (res: Z) (retval: Z) (clist'_2: (@list (@list Z))) (pcnt'_2: Z) (ccnt'_2: Z) (res_2: Z) (retval_2: Z) (clist'': (@list (@list Z))) (pcnt'': Z) (ccnt'': Z) ,
  [| (((prop_cnt_inf (clist'')) + 1 ) <= (pcnt'' + 1 )) |] 
  &&  [| ((pcnt'' + 1 ) <> 0) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist'')) = ccnt'') |] 
  &&  [| ((prop_cnt_inf (clist'')) <= pcnt'') |] 
  &&  [| (pcnt'' >= 0) |] 
  &&  [| ((make_prop2cnf_ret ((make_predata (clist'_2) (pcnt'_2) (ccnt'_2))) (res_2)) = (prop2cnf_logic (rt) ((make_predata (clist') (pcnt') (ccnt'))))) |] 
  &&  [| (retval_2 = res_2) |] 
  &&  [| (res_2 <> 0) |] 
  &&  [| (res_2 <= pcnt'_2) |] 
  &&  [| ((-res_2) <= pcnt'_2) |] 
  &&  [| ((make_prop2cnf_ret ((make_predata (clist') (pcnt') (ccnt'))) (res)) = (prop2cnf_logic (lt) ((make_predata (clist) (pcnt) (ccnt))))) |] 
  &&  [| (retval = res) |] 
  &&  [| (res <> 0) |] 
  &&  [| (res <= pcnt') |] 
  &&  [| ((-res) <= pcnt') |] 
  &&  [| ((prop_cnt_inf_SmtProp (lt)) <= pcnt) |] 
  &&  [| ((prop_cnt_inf_SmtProp (rt)) <= pcnt) |] 
  &&  [| (prop = (SmtB (op) (lt) (rt))) |] 
  &&  [| (p_pre <> 0) |] 
  &&  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t = 5) |]
  &&  (store_predata data_pre clist'' (pcnt'' + 1 ) ccnt'' )
  **  (store_SmtProp z rt )
  **  (store_SmtProp y lt )
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "op")) # Int  |-> (SmtPBID (op)))
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop1")) # Ptr  |-> y)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop2")) # Ptr  |-> z)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
|--
  [| (retval <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| ((pcnt'' + 1 ) <> 0) |] 
  &&  [| (retval <= (pcnt'' + 1 )) |] 
  &&  [| (retval_2 <= (pcnt'' + 1 )) |] 
  &&  [| ((pcnt'' + 1 ) <= (pcnt'' + 1 )) |] 
  &&  [| ((-retval) <= (pcnt'' + 1 )) |] 
  &&  [| ((-retval_2) <= (pcnt'' + 1 )) |] 
  &&  [| ((-(pcnt'' + 1 )) <= (pcnt'' + 1 )) |] 
  &&  [| (((prop_cnt_inf (clist'')) + 1 ) <= (pcnt'' + 1 )) |] 
  &&  [| ((SmtPBID (op)) = (SmtPBID (op))) |] 
  &&  [| ((-res_2) <= (pcnt'' + 1 )) |] 
  &&  [| ((-res) <= (pcnt'' + 1 )) |] 
  &&  [| (res_2 <= (pcnt'' + 1 )) |] 
  &&  [| (res <= (pcnt'' + 1 )) |] 
  &&  [| (((prop_cnt_inf (clist'')) + 1 ) <= (pcnt'' + 1 )) |] 
  &&  [| ((pcnt'' + 1 ) <> 0) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist'')) = ccnt'') |] 
  &&  [| ((prop_cnt_inf (clist'')) <= pcnt'') |] 
  &&  [| (pcnt'' >= 0) |] 
  &&  [| ((make_prop2cnf_ret ((make_predata (clist'_2) (pcnt'_2) (ccnt'_2))) (res_2)) = (prop2cnf_logic (rt) ((make_predata (clist') (pcnt') (ccnt'))))) |] 
  &&  [| (retval_2 = res_2) |] 
  &&  [| (res_2 <> 0) |] 
  &&  [| (res_2 <= pcnt'_2) |] 
  &&  [| ((-res_2) <= pcnt'_2) |] 
  &&  [| ((make_prop2cnf_ret ((make_predata (clist') (pcnt') (ccnt'))) (res)) = (prop2cnf_logic (lt) ((make_predata (clist) (pcnt) (ccnt))))) |] 
  &&  [| (retval = res) |] 
  &&  [| (res <> 0) |] 
  &&  [| (res <= pcnt') |] 
  &&  [| ((-res) <= pcnt') |] 
  &&  [| ((prop_cnt_inf_SmtProp (lt)) <= pcnt) |] 
  &&  [| ((prop_cnt_inf_SmtProp (rt)) <= pcnt) |] 
  &&  [| (prop = (SmtB (op) (lt) (rt))) |] 
  &&  [| (p_pre <> 0) |] 
  &&  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t = 5) |]
  &&  (store_predata data_pre clist'' (pcnt'' + 1 ) ccnt'' )
  **  (store_SmtProp z rt )
  **  (store_SmtProp y lt )
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "op")) # Int  |-> (SmtPBID (op)))
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop1")) # Ptr  |-> y)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop2")) # Ptr  |-> z)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
.

Definition prop2cnf_partial_solve_wit_10 := prop2cnf_partial_solve_wit_10_pure -> prop2cnf_partial_solve_wit_10_aux.

Definition prop2cnf_partial_solve_wit_11_pure := 
forall (data_pre: Z) (p_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (prop: smt_prop) (t: Z) ,
  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t <> 5) |] 
  &&  [| (t = 6) |]
  &&  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> t)
  **  (store_SmtProp' p_pre prop )
  **  ((( &( "res" ) )) # Int  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| ((SmtPTID (prop)) = (SmtPTID (prop))) |] 
  &&  [| ((SmtPTID (prop)) = 6) |]
.

Definition prop2cnf_partial_solve_wit_11_aux := 
forall (data_pre: Z) (p_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (prop: smt_prop) (t: Z) ,
  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t <> 5) |] 
  &&  [| (t = 6) |]
  &&  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> t)
  **  (store_SmtProp' p_pre prop )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| ((SmtPTID (prop)) = (SmtPTID (prop))) |] 
  &&  [| ((SmtPTID (prop)) = 6) |] 
  &&  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t <> 5) |] 
  &&  [| (t = 6) |]
  &&  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
  **  (store_SmtProp' p_pre prop )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition prop2cnf_partial_solve_wit_11 := prop2cnf_partial_solve_wit_11_pure -> prop2cnf_partial_solve_wit_11_aux.

Definition prop2cnf_partial_solve_wit_12_pure := 
forall (data_pre: Z) (p_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (prop: smt_prop) (t: Z) (y: Z) (op: SmtPropUop) (sub_prop: smt_prop) ,
  [| (prop = (SmtU (op) (sub_prop))) |] 
  &&  [| (p_pre <> 0) |] 
  &&  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t <> 5) |] 
  &&  [| (t = 6) |]
  &&  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "op")) # Int  |-> (SmtPUID (op)))
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "prop1")) # Ptr  |-> y)
  **  (store_SmtProp y sub_prop )
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
  **  ((( &( "res" ) )) # Int  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |]
.

Definition prop2cnf_partial_solve_wit_12_aux := 
forall (data_pre: Z) (p_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (prop: smt_prop) (t: Z) (y: Z) (op: SmtPropUop) (sub_prop: smt_prop) ,
  [| (prop = (SmtU (op) (sub_prop))) |] 
  &&  [| (p_pre <> 0) |] 
  &&  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t <> 5) |] 
  &&  [| (t = 6) |]
  &&  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "op")) # Int  |-> (SmtPUID (op)))
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "prop1")) # Ptr  |-> y)
  **  (store_SmtProp y sub_prop )
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (prop = (SmtU (op) (sub_prop))) |] 
  &&  [| (p_pre <> 0) |] 
  &&  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t <> 5) |] 
  &&  [| (t = 6) |]
  &&  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "op")) # Int  |-> (SmtPUID (op)))
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "prop1")) # Ptr  |-> y)
  **  (store_SmtProp y sub_prop )
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition prop2cnf_partial_solve_wit_12 := prop2cnf_partial_solve_wit_12_pure -> prop2cnf_partial_solve_wit_12_aux.

Definition prop2cnf_partial_solve_wit_13_pure := 
forall (data_pre: Z) (p_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (prop: smt_prop) (t: Z) (y: Z) (op: SmtPropUop) (sub_prop: smt_prop) ,
  [| ((prop_cnt_inf_SmtProp (sub_prop)) <= pcnt) |] 
  &&  [| (prop = (SmtU (op) (sub_prop))) |] 
  &&  [| (p_pre <> 0) |] 
  &&  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t <> 5) |] 
  &&  [| (t = 6) |]
  &&  ((( &( "p1" ) )) # Int  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "op")) # Int  |-> (SmtPUID (op)))
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "prop1")) # Ptr  |-> y)
  **  (store_SmtProp y sub_prop )
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
  **  ((( &( "res" ) )) # Int  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| ((prop_cnt_inf_SmtProp (sub_prop)) <= pcnt) |]
.

Definition prop2cnf_partial_solve_wit_13_aux := 
forall (data_pre: Z) (p_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (prop: smt_prop) (t: Z) (y: Z) (op: SmtPropUop) (sub_prop: smt_prop) ,
  [| ((prop_cnt_inf_SmtProp (sub_prop)) <= pcnt) |] 
  &&  [| (prop = (SmtU (op) (sub_prop))) |] 
  &&  [| (p_pre <> 0) |] 
  &&  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t <> 5) |] 
  &&  [| (t = 6) |]
  &&  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "op")) # Int  |-> (SmtPUID (op)))
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "prop1")) # Ptr  |-> y)
  **  (store_SmtProp y sub_prop )
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| ((prop_cnt_inf_SmtProp (sub_prop)) <= pcnt) |] 
  &&  [| ((prop_cnt_inf_SmtProp (sub_prop)) <= pcnt) |] 
  &&  [| (prop = (SmtU (op) (sub_prop))) |] 
  &&  [| (p_pre <> 0) |] 
  &&  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t <> 5) |] 
  &&  [| (t = 6) |]
  &&  (store_SmtProp y sub_prop )
  **  (store_predata data_pre clist pcnt ccnt )
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "op")) # Int  |-> (SmtPUID (op)))
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "prop1")) # Ptr  |-> y)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
.

Definition prop2cnf_partial_solve_wit_13 := prop2cnf_partial_solve_wit_13_pure -> prop2cnf_partial_solve_wit_13_aux.

Definition prop2cnf_partial_solve_wit_14 := 
forall (data_pre: Z) (p_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (prop: smt_prop) (t: Z) (y: Z) (op: SmtPropUop) (sub_prop: smt_prop) (clist': (@list (@list Z))) (pcnt': Z) (ccnt': Z) (res: Z) (retval: Z) (clist'': (@list (@list Z))) (pcnt'': Z) (ccnt'': Z) ,
  [| ((make_prop2cnf_ret ((make_predata (clist') (pcnt') (ccnt'))) (res)) = (prop2cnf_logic (sub_prop) ((make_predata (clist) (pcnt) (ccnt))))) |] 
  &&  [| (retval = res) |] 
  &&  [| (res <> 0) |] 
  &&  [| (res <= pcnt') |] 
  &&  [| ((-res) <= pcnt') |] 
  &&  [| ((prop_cnt_inf_SmtProp (sub_prop)) <= pcnt) |] 
  &&  [| (prop = (SmtU (op) (sub_prop))) |] 
  &&  [| (p_pre <> 0) |] 
  &&  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t <> 5) |] 
  &&  [| (t = 6) |]
  &&  (store_predata data_pre clist'' pcnt'' ccnt'' )
  **  (store_SmtProp y sub_prop )
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "op")) # Int  |-> (SmtPUID (op)))
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "prop1")) # Ptr  |-> y)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
|--
  [| ((make_prop2cnf_ret ((make_predata (clist') (pcnt') (ccnt'))) (res)) = (prop2cnf_logic (sub_prop) ((make_predata (clist) (pcnt) (ccnt))))) |] 
  &&  [| (retval = res) |] 
  &&  [| (res <> 0) |] 
  &&  [| (res <= pcnt') |] 
  &&  [| ((-res) <= pcnt') |] 
  &&  [| ((prop_cnt_inf_SmtProp (sub_prop)) <= pcnt) |] 
  &&  [| (prop = (SmtU (op) (sub_prop))) |] 
  &&  [| (p_pre <> 0) |] 
  &&  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t <> 5) |] 
  &&  [| (t = 6) |]
  &&  (store_predata data_pre clist'' pcnt'' ccnt'' )
  **  (store_SmtProp y sub_prop )
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "op")) # Int  |-> (SmtPUID (op)))
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "prop1")) # Ptr  |-> y)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
.

Definition prop2cnf_partial_solve_wit_15_pure := 
forall (data_pre: Z) (p_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (prop: smt_prop) (t: Z) (y: Z) (op: SmtPropUop) (sub_prop: smt_prop) (clist': (@list (@list Z))) (pcnt': Z) (ccnt': Z) (res: Z) (retval: Z) (clist'': (@list (@list Z))) (pcnt'': Z) (ccnt'': Z) (y'': Z) ,
  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist'')) = ccnt'') |] 
  &&  [| ((prop_cnt_inf (clist'')) <= pcnt'') |] 
  &&  [| (pcnt'' >= 0) |] 
  &&  [| ((make_prop2cnf_ret ((make_predata (clist') (pcnt') (ccnt'))) (res)) = (prop2cnf_logic (sub_prop) ((make_predata (clist) (pcnt) (ccnt))))) |] 
  &&  [| (retval = res) |] 
  &&  [| (res <> 0) |] 
  &&  [| (res <= pcnt') |] 
  &&  [| ((-res) <= pcnt') |] 
  &&  [| ((prop_cnt_inf_SmtProp (sub_prop)) <= pcnt) |] 
  &&  [| (prop = (SmtU (op) (sub_prop))) |] 
  &&  [| (p_pre <> 0) |] 
  &&  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t <> 5) |] 
  &&  [| (t = 6) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y'')
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> (pcnt'' + 1 ))
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt'')
  **  (sll_cnf_list y'' clist'' )
  **  (store_SmtProp y sub_prop )
  **  ((( &( "p1" ) )) # Int  |-> retval)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "op")) # Int  |-> (SmtPUID (op)))
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "prop1")) # Ptr  |-> y)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
  **  ((( &( "res" ) )) # Int  |-> (pcnt'' + 1 ))
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
|--
  [| (pcnt'' >= 0) |] 
  &&  [| ((pcnt'' + 1 ) = (pcnt'' + 1 )) |]
.

Definition prop2cnf_partial_solve_wit_15_aux := 
forall (data_pre: Z) (p_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (prop: smt_prop) (t: Z) (y: Z) (op: SmtPropUop) (sub_prop: smt_prop) (clist': (@list (@list Z))) (pcnt': Z) (ccnt': Z) (res: Z) (retval: Z) (clist'': (@list (@list Z))) (pcnt'': Z) (ccnt'': Z) (y'': Z) ,
  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist'')) = ccnt'') |] 
  &&  [| ((prop_cnt_inf (clist'')) <= pcnt'') |] 
  &&  [| (pcnt'' >= 0) |] 
  &&  [| ((make_prop2cnf_ret ((make_predata (clist') (pcnt') (ccnt'))) (res)) = (prop2cnf_logic (sub_prop) ((make_predata (clist) (pcnt) (ccnt))))) |] 
  &&  [| (retval = res) |] 
  &&  [| (res <> 0) |] 
  &&  [| (res <= pcnt') |] 
  &&  [| ((-res) <= pcnt') |] 
  &&  [| ((prop_cnt_inf_SmtProp (sub_prop)) <= pcnt) |] 
  &&  [| (prop = (SmtU (op) (sub_prop))) |] 
  &&  [| (p_pre <> 0) |] 
  &&  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t <> 5) |] 
  &&  [| (t = 6) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y'')
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> (pcnt'' + 1 ))
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt'')
  **  (sll_cnf_list y'' clist'' )
  **  (store_SmtProp y sub_prop )
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "op")) # Int  |-> (SmtPUID (op)))
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "prop1")) # Ptr  |-> y)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
|--
  [| (pcnt'' >= 0) |] 
  &&  [| ((pcnt'' + 1 ) = (pcnt'' + 1 )) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist'')) = ccnt'') |] 
  &&  [| ((prop_cnt_inf (clist'')) <= pcnt'') |] 
  &&  [| (pcnt'' >= 0) |] 
  &&  [| ((make_prop2cnf_ret ((make_predata (clist') (pcnt') (ccnt'))) (res)) = (prop2cnf_logic (sub_prop) ((make_predata (clist) (pcnt) (ccnt))))) |] 
  &&  [| (retval = res) |] 
  &&  [| (res <> 0) |] 
  &&  [| (res <= pcnt') |] 
  &&  [| ((-res) <= pcnt') |] 
  &&  [| ((prop_cnt_inf_SmtProp (sub_prop)) <= pcnt) |] 
  &&  [| (prop = (SmtU (op) (sub_prop))) |] 
  &&  [| (p_pre <> 0) |] 
  &&  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t <> 5) |] 
  &&  [| (t = 6) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y'')
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> (pcnt'' + 1 ))
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt'')
  **  (sll_cnf_list y'' clist'' )
  **  (store_SmtProp y sub_prop )
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "op")) # Int  |-> (SmtPUID (op)))
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "prop1")) # Ptr  |-> y)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
.

Definition prop2cnf_partial_solve_wit_15 := prop2cnf_partial_solve_wit_15_pure -> prop2cnf_partial_solve_wit_15_aux.

Definition prop2cnf_partial_solve_wit_16_pure := 
forall (data_pre: Z) (p_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (prop: smt_prop) (t: Z) (y: Z) (op: SmtPropUop) (sub_prop: smt_prop) (clist': (@list (@list Z))) (pcnt': Z) (ccnt': Z) (res: Z) (retval: Z) (clist'': (@list (@list Z))) (pcnt'': Z) (ccnt'': Z) (y'': Z) ,
  [| ((pcnt'' + 1 ) <> 0) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist'')) = ccnt'') |] 
  &&  [| ((prop_cnt_inf (clist'')) <= pcnt'') |] 
  &&  [| (pcnt'' >= 0) |] 
  &&  [| ((make_prop2cnf_ret ((make_predata (clist') (pcnt') (ccnt'))) (res)) = (prop2cnf_logic (sub_prop) ((make_predata (clist) (pcnt) (ccnt))))) |] 
  &&  [| (retval = res) |] 
  &&  [| (res <> 0) |] 
  &&  [| (res <= pcnt') |] 
  &&  [| ((-res) <= pcnt') |] 
  &&  [| ((prop_cnt_inf_SmtProp (sub_prop)) <= pcnt) |] 
  &&  [| (prop = (SmtU (op) (sub_prop))) |] 
  &&  [| (p_pre <> 0) |] 
  &&  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t <> 5) |] 
  &&  [| (t = 6) |]
  &&  ((( &( "res" ) )) # Int  |-> (pcnt'' + 1 ))
  **  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y'')
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> (pcnt'' + 1 ))
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt'')
  **  (sll_cnf_list y'' clist'' )
  **  (store_SmtProp y sub_prop )
  **  ((( &( "p1" ) )) # Int  |-> retval)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "op")) # Int  |-> (SmtPUID (op)))
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "prop1")) # Ptr  |-> y)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
|--
  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist'')) = ccnt'') |] 
  &&  [| ((prop_cnt_inf (clist'')) <= pcnt'') |]
.

Definition prop2cnf_partial_solve_wit_16_aux := 
forall (data_pre: Z) (p_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (prop: smt_prop) (t: Z) (y: Z) (op: SmtPropUop) (sub_prop: smt_prop) (clist': (@list (@list Z))) (pcnt': Z) (ccnt': Z) (res: Z) (retval: Z) (clist'': (@list (@list Z))) (pcnt'': Z) (ccnt'': Z) (y'': Z) ,
  [| ((pcnt'' + 1 ) <> 0) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist'')) = ccnt'') |] 
  &&  [| ((prop_cnt_inf (clist'')) <= pcnt'') |] 
  &&  [| (pcnt'' >= 0) |] 
  &&  [| ((make_prop2cnf_ret ((make_predata (clist') (pcnt') (ccnt'))) (res)) = (prop2cnf_logic (sub_prop) ((make_predata (clist) (pcnt) (ccnt))))) |] 
  &&  [| (retval = res) |] 
  &&  [| (res <> 0) |] 
  &&  [| (res <= pcnt') |] 
  &&  [| ((-res) <= pcnt') |] 
  &&  [| ((prop_cnt_inf_SmtProp (sub_prop)) <= pcnt) |] 
  &&  [| (prop = (SmtU (op) (sub_prop))) |] 
  &&  [| (p_pre <> 0) |] 
  &&  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t <> 5) |] 
  &&  [| (t = 6) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y'')
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> (pcnt'' + 1 ))
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt'')
  **  (sll_cnf_list y'' clist'' )
  **  (store_SmtProp y sub_prop )
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "op")) # Int  |-> (SmtPUID (op)))
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "prop1")) # Ptr  |-> y)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
|--
  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist'')) = ccnt'') |] 
  &&  [| ((prop_cnt_inf (clist'')) <= pcnt'') |] 
  &&  [| ((pcnt'' + 1 ) <> 0) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist'')) = ccnt'') |] 
  &&  [| ((prop_cnt_inf (clist'')) <= pcnt'') |] 
  &&  [| (pcnt'' >= 0) |] 
  &&  [| ((make_prop2cnf_ret ((make_predata (clist') (pcnt') (ccnt'))) (res)) = (prop2cnf_logic (sub_prop) ((make_predata (clist) (pcnt) (ccnt))))) |] 
  &&  [| (retval = res) |] 
  &&  [| (res <> 0) |] 
  &&  [| (res <= pcnt') |] 
  &&  [| ((-res) <= pcnt') |] 
  &&  [| ((prop_cnt_inf_SmtProp (sub_prop)) <= pcnt) |] 
  &&  [| (prop = (SmtU (op) (sub_prop))) |] 
  &&  [| (p_pre <> 0) |] 
  &&  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t <> 5) |] 
  &&  [| (t = 6) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y'')
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> (pcnt'' + 1 ))
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt'')
  **  (sll_cnf_list y'' clist'' )
  **  (store_SmtProp y sub_prop )
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "op")) # Int  |-> (SmtPUID (op)))
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "prop1")) # Ptr  |-> y)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
.

Definition prop2cnf_partial_solve_wit_16 := prop2cnf_partial_solve_wit_16_pure -> prop2cnf_partial_solve_wit_16_aux.

Definition prop2cnf_partial_solve_wit_17_pure := 
forall (data_pre: Z) (p_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (prop: smt_prop) (t: Z) (y: Z) (op: SmtPropUop) (sub_prop: smt_prop) (clist': (@list (@list Z))) (pcnt': Z) (ccnt': Z) (res: Z) (retval: Z) (clist'': (@list (@list Z))) (pcnt'': Z) (ccnt'': Z) ,
  [| ((pcnt'' + 1 ) <> 0) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist'')) = ccnt'') |] 
  &&  [| ((prop_cnt_inf (clist'')) <= pcnt'') |] 
  &&  [| (pcnt'' >= 0) |] 
  &&  [| ((make_prop2cnf_ret ((make_predata (clist') (pcnt') (ccnt'))) (res)) = (prop2cnf_logic (sub_prop) ((make_predata (clist) (pcnt) (ccnt))))) |] 
  &&  [| (retval = res) |] 
  &&  [| (res <> 0) |] 
  &&  [| (res <= pcnt') |] 
  &&  [| ((-res) <= pcnt') |] 
  &&  [| ((prop_cnt_inf_SmtProp (sub_prop)) <= pcnt) |] 
  &&  [| (prop = (SmtU (op) (sub_prop))) |] 
  &&  [| (p_pre <> 0) |] 
  &&  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t <> 5) |] 
  &&  [| (t = 6) |]
  &&  (store_predata data_pre clist'' (pcnt'' + 1 ) ccnt'' )
  **  ((( &( "res" ) )) # Int  |-> (pcnt'' + 1 ))
  **  (store_SmtProp y sub_prop )
  **  ((( &( "p1" ) )) # Int  |-> retval)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "op")) # Int  |-> (SmtPUID (op)))
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "prop1")) # Ptr  |-> y)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
|--
  [| ((prop_cnt_inf (clist'')) <= pcnt'') |]
.

Definition prop2cnf_partial_solve_wit_17_aux := 
forall (data_pre: Z) (p_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (prop: smt_prop) (t: Z) (y: Z) (op: SmtPropUop) (sub_prop: smt_prop) (clist': (@list (@list Z))) (pcnt': Z) (ccnt': Z) (res: Z) (retval: Z) (clist'': (@list (@list Z))) (pcnt'': Z) (ccnt'': Z) ,
  [| ((pcnt'' + 1 ) <> 0) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist'')) = ccnt'') |] 
  &&  [| ((prop_cnt_inf (clist'')) <= pcnt'') |] 
  &&  [| (pcnt'' >= 0) |] 
  &&  [| ((make_prop2cnf_ret ((make_predata (clist') (pcnt') (ccnt'))) (res)) = (prop2cnf_logic (sub_prop) ((make_predata (clist) (pcnt) (ccnt))))) |] 
  &&  [| (retval = res) |] 
  &&  [| (res <> 0) |] 
  &&  [| (res <= pcnt') |] 
  &&  [| ((-res) <= pcnt') |] 
  &&  [| ((prop_cnt_inf_SmtProp (sub_prop)) <= pcnt) |] 
  &&  [| (prop = (SmtU (op) (sub_prop))) |] 
  &&  [| (p_pre <> 0) |] 
  &&  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t <> 5) |] 
  &&  [| (t = 6) |]
  &&  (store_predata data_pre clist'' (pcnt'' + 1 ) ccnt'' )
  **  (store_SmtProp y sub_prop )
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "op")) # Int  |-> (SmtPUID (op)))
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "prop1")) # Ptr  |-> y)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
|--
  [| ((prop_cnt_inf (clist'')) <= pcnt'') |] 
  &&  [| ((pcnt'' + 1 ) <> 0) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist'')) = ccnt'') |] 
  &&  [| ((prop_cnt_inf (clist'')) <= pcnt'') |] 
  &&  [| (pcnt'' >= 0) |] 
  &&  [| ((make_prop2cnf_ret ((make_predata (clist') (pcnt') (ccnt'))) (res)) = (prop2cnf_logic (sub_prop) ((make_predata (clist) (pcnt) (ccnt))))) |] 
  &&  [| (retval = res) |] 
  &&  [| (res <> 0) |] 
  &&  [| (res <= pcnt') |] 
  &&  [| ((-res) <= pcnt') |] 
  &&  [| ((prop_cnt_inf_SmtProp (sub_prop)) <= pcnt) |] 
  &&  [| (prop = (SmtU (op) (sub_prop))) |] 
  &&  [| (p_pre <> 0) |] 
  &&  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t <> 5) |] 
  &&  [| (t = 6) |]
  &&  (store_predata data_pre clist'' (pcnt'' + 1 ) ccnt'' )
  **  (store_SmtProp y sub_prop )
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "op")) # Int  |-> (SmtPUID (op)))
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "prop1")) # Ptr  |-> y)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
.

Definition prop2cnf_partial_solve_wit_17 := prop2cnf_partial_solve_wit_17_pure -> prop2cnf_partial_solve_wit_17_aux.

Definition prop2cnf_partial_solve_wit_18_pure := 
forall (data_pre: Z) (p_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (prop: smt_prop) (t: Z) (y: Z) (op: SmtPropUop) (sub_prop: smt_prop) (clist': (@list (@list Z))) (pcnt': Z) (ccnt': Z) (res: Z) (retval: Z) (clist'': (@list (@list Z))) (pcnt'': Z) (ccnt'': Z) ,
  [| (((prop_cnt_inf (clist'')) + 1 ) <= (pcnt'' + 1 )) |] 
  &&  [| ((pcnt'' + 1 ) <> 0) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist'')) = ccnt'') |] 
  &&  [| ((prop_cnt_inf (clist'')) <= pcnt'') |] 
  &&  [| (pcnt'' >= 0) |] 
  &&  [| ((make_prop2cnf_ret ((make_predata (clist') (pcnt') (ccnt'))) (res)) = (prop2cnf_logic (sub_prop) ((make_predata (clist) (pcnt) (ccnt))))) |] 
  &&  [| (retval = res) |] 
  &&  [| (res <> 0) |] 
  &&  [| (res <= pcnt') |] 
  &&  [| ((-res) <= pcnt') |] 
  &&  [| ((prop_cnt_inf_SmtProp (sub_prop)) <= pcnt) |] 
  &&  [| (prop = (SmtU (op) (sub_prop))) |] 
  &&  [| (p_pre <> 0) |] 
  &&  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t <> 5) |] 
  &&  [| (t = 6) |]
  &&  (store_predata data_pre clist'' (pcnt'' + 1 ) ccnt'' )
  **  ((( &( "res" ) )) # Int  |-> (pcnt'' + 1 ))
  **  (store_SmtProp y sub_prop )
  **  ((( &( "p1" ) )) # Int  |-> retval)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "op")) # Int  |-> (SmtPUID (op)))
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "prop1")) # Ptr  |-> y)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
|--
  [| (retval <> 0) |] 
  &&  [| ((pcnt'' + 1 ) <> 0) |] 
  &&  [| (((prop_cnt_inf (clist'')) + 1 ) <= (pcnt'' + 1 )) |] 
  &&  [| (retval <= (pcnt'' + 1 )) |] 
  &&  [| ((pcnt'' + 1 ) <= (pcnt'' + 1 )) |] 
  &&  [| ((-retval) <= (pcnt'' + 1 )) |] 
  &&  [| ((-(pcnt'' + 1 )) <= (pcnt'' + 1 )) |] 
  &&  [| ((-res) <= (pcnt'' + 1 )) |] 
  &&  [| (res <= (pcnt'' + 1 )) |]
.

Definition prop2cnf_partial_solve_wit_18_aux := 
forall (data_pre: Z) (p_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (prop: smt_prop) (t: Z) (y: Z) (op: SmtPropUop) (sub_prop: smt_prop) (clist': (@list (@list Z))) (pcnt': Z) (ccnt': Z) (res: Z) (retval: Z) (clist'': (@list (@list Z))) (pcnt'': Z) (ccnt'': Z) ,
  [| (((prop_cnt_inf (clist'')) + 1 ) <= (pcnt'' + 1 )) |] 
  &&  [| ((pcnt'' + 1 ) <> 0) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist'')) = ccnt'') |] 
  &&  [| ((prop_cnt_inf (clist'')) <= pcnt'') |] 
  &&  [| (pcnt'' >= 0) |] 
  &&  [| ((make_prop2cnf_ret ((make_predata (clist') (pcnt') (ccnt'))) (res)) = (prop2cnf_logic (sub_prop) ((make_predata (clist) (pcnt) (ccnt))))) |] 
  &&  [| (retval = res) |] 
  &&  [| (res <> 0) |] 
  &&  [| (res <= pcnt') |] 
  &&  [| ((-res) <= pcnt') |] 
  &&  [| ((prop_cnt_inf_SmtProp (sub_prop)) <= pcnt) |] 
  &&  [| (prop = (SmtU (op) (sub_prop))) |] 
  &&  [| (p_pre <> 0) |] 
  &&  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t <> 5) |] 
  &&  [| (t = 6) |]
  &&  (store_predata data_pre clist'' (pcnt'' + 1 ) ccnt'' )
  **  (store_SmtProp y sub_prop )
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "op")) # Int  |-> (SmtPUID (op)))
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "prop1")) # Ptr  |-> y)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
|--
  [| (retval <> 0) |] 
  &&  [| ((pcnt'' + 1 ) <> 0) |] 
  &&  [| (((prop_cnt_inf (clist'')) + 1 ) <= (pcnt'' + 1 )) |] 
  &&  [| (retval <= (pcnt'' + 1 )) |] 
  &&  [| ((pcnt'' + 1 ) <= (pcnt'' + 1 )) |] 
  &&  [| ((-retval) <= (pcnt'' + 1 )) |] 
  &&  [| ((-(pcnt'' + 1 )) <= (pcnt'' + 1 )) |] 
  &&  [| ((-res) <= (pcnt'' + 1 )) |] 
  &&  [| (res <= (pcnt'' + 1 )) |] 
  &&  [| (((prop_cnt_inf (clist'')) + 1 ) <= (pcnt'' + 1 )) |] 
  &&  [| ((pcnt'' + 1 ) <> 0) |] 
  &&  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist'')) = ccnt'') |] 
  &&  [| ((prop_cnt_inf (clist'')) <= pcnt'') |] 
  &&  [| (pcnt'' >= 0) |] 
  &&  [| ((make_prop2cnf_ret ((make_predata (clist') (pcnt') (ccnt'))) (res)) = (prop2cnf_logic (sub_prop) ((make_predata (clist) (pcnt) (ccnt))))) |] 
  &&  [| (retval = res) |] 
  &&  [| (res <> 0) |] 
  &&  [| (res <= pcnt') |] 
  &&  [| ((-res) <= pcnt') |] 
  &&  [| ((prop_cnt_inf_SmtProp (sub_prop)) <= pcnt) |] 
  &&  [| (prop = (SmtU (op) (sub_prop))) |] 
  &&  [| (p_pre <> 0) |] 
  &&  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t <> 5) |] 
  &&  [| (t = 6) |]
  &&  (store_predata data_pre clist'' (pcnt'' + 1 ) ccnt'' )
  **  (store_SmtProp y sub_prop )
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "op")) # Int  |-> (SmtPUID (op)))
  **  ((&((p_pre)  # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "prop1")) # Ptr  |-> y)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
.

Definition prop2cnf_partial_solve_wit_18 := prop2cnf_partial_solve_wit_18_pure -> prop2cnf_partial_solve_wit_18_aux.

Definition prop2cnf_partial_solve_wit_19_pure := 
forall (data_pre: Z) (p_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (prop: smt_prop) (t: Z) ,
  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t <> 5) |] 
  &&  [| (t <> 6) |] 
  &&  [| (t = 7) |]
  &&  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> t)
  **  (store_SmtProp' p_pre prop )
  **  ((( &( "res" ) )) # Int  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (7 = 7) |] 
  &&  [| (7 = (SmtPTID (prop))) |]
.

Definition prop2cnf_partial_solve_wit_19_aux := 
forall (data_pre: Z) (p_pre: Z) (ccnt: Z) (pcnt: Z) (clist: (@list (@list Z))) (prop: smt_prop) (t: Z) ,
  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t <> 5) |] 
  &&  [| (t <> 6) |] 
  &&  [| (t = 7) |]
  &&  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> t)
  **  (store_SmtProp' p_pre prop )
  **  (store_predata data_pre clist pcnt ccnt )
|--
  [| (7 = 7) |] 
  &&  [| (7 = (SmtPTID (prop))) |] 
  &&  [| (t = (SmtPTID (prop))) |] 
  &&  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |] 
  &&  [| (t <> 5) |] 
  &&  [| (t <> 6) |] 
  &&  [| (t = 7) |]
  &&  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> 7)
  **  (store_SmtProp' p_pre prop )
  **  (store_predata data_pre clist pcnt ccnt )
.

Definition prop2cnf_partial_solve_wit_19 := prop2cnf_partial_solve_wit_19_pure -> prop2cnf_partial_solve_wit_19_aux.

Definition prop2cnf_which_implies_wit_1 := 
forall (prop: smt_prop) (p: Z) ,
  (store_SmtProp p prop )
|--
  EX (t: Z) ,
  [| (t = (SmtPTID (prop))) |]
  &&  ((&((p)  # "SmtProp" ->ₛ "type")) # Int  |-> t)
  **  (store_SmtProp' p prop )
.

Definition prop2cnf_which_implies_wit_2 := 
forall (p_pre: Z) (prop: smt_prop) (p_pre_type: Z) (p: Z) ,
  [| (p_pre_type = (SmtPTID (prop))) |] 
  &&  [| (p_pre_type = 5) |]
  &&  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> p_pre_type)
  **  (store_SmtProp' p prop )
|--
  EX (z: Z)  (y: Z)  (op: SmtPropBop)  (lt: smt_prop)  (rt: smt_prop) ,
  [| (prop = (SmtB (op) (lt) (rt))) |] 
  &&  [| (p_pre <> 0) |]
  &&  ((&((p)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "op")) # Int  |-> (SmtPBID (op)))
  **  ((&((p)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop1")) # Ptr  |-> y)
  **  ((&((p)  # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop2")) # Ptr  |-> z)
  **  (store_SmtProp y lt )
  **  (store_SmtProp z rt )
  **  ((&((p)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
.

Definition prop2cnf_which_implies_wit_3 := 
forall (pcnt: Z) (prop: smt_prop) (lt: smt_prop) (rt: smt_prop) ,
  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |]
  &&  emp
|--
  [| ((prop_cnt_inf_SmtProp (lt)) <= pcnt) |] 
  &&  [| ((prop_cnt_inf_SmtProp (rt)) <= pcnt) |]
  &&  emp
.

Definition prop2cnf_which_implies_wit_4 := 
forall (data_pre: Z) (clist'': (@list (@list Z))) (pcnt'': Z) (ccnt'': Z) ,
  (store_predata data_pre clist'' pcnt'' ccnt'' )
|--
  EX (y'': Z) ,
  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist'')) = ccnt'') |] 
  &&  [| ((prop_cnt_inf (clist'')) <= pcnt'') |] 
  &&  [| (pcnt'' >= 0) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y'')
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt'')
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt'')
  **  (sll_cnf_list y'' clist'' )
.

Definition prop2cnf_which_implies_wit_5 := 
forall (pcnt'': Z) (res: Z) ,
  [| (pcnt'' >= 0) |] 
  &&  [| (res = (pcnt'' + 1 )) |]
  &&  emp
|--
  [| (res <> 0) |]
  &&  emp
.

Definition prop2cnf_which_implies_wit_6 := 
forall (data_pre: Z) (clist'': (@list (@list Z))) (pcnt'': Z) (ccnt'': Z) (y'': Z) ,
  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist'')) = ccnt'') |] 
  &&  [| ((prop_cnt_inf (clist'')) <= pcnt'') |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y'')
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> (pcnt'' + 1 ))
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt'')
  **  (sll_cnf_list y'' clist'' )
|--
  (store_predata data_pre clist'' (pcnt'' + 1 ) ccnt'' )
.

Definition prop2cnf_which_implies_wit_7 := 
forall (clist'': (@list (@list Z))) (pcnt'': Z) ,
  [| ((prop_cnt_inf (clist'')) <= pcnt'') |]
  &&  emp
|--
  [| (((prop_cnt_inf (clist'')) + 1 ) <= (pcnt'' + 1 )) |]
  &&  emp
.

Definition prop2cnf_which_implies_wit_8 := 
forall (p_pre: Z) (prop: smt_prop) (p_pre_type: Z) (p: Z) ,
  [| (p_pre_type = (SmtPTID (prop))) |] 
  &&  [| (p_pre_type = 6) |]
  &&  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> p_pre_type)
  **  (store_SmtProp' p prop )
|--
  EX (y: Z)  (op: SmtPropUop)  (sub_prop: smt_prop) ,
  [| (prop = (SmtU (op) (sub_prop))) |] 
  &&  [| (p_pre <> 0) |]
  &&  ((&((p)  # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "op")) # Int  |-> (SmtPUID (op)))
  **  ((&((p)  # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "prop1")) # Ptr  |-> y)
  **  (store_SmtProp y sub_prop )
  **  ((&((p)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
.

Definition prop2cnf_which_implies_wit_9 := 
forall (pcnt: Z) (prop: smt_prop) (sub_prop: smt_prop) ,
  [| ((prop_cnt_inf_SmtProp (prop)) <= pcnt) |]
  &&  emp
|--
  [| ((prop_cnt_inf_SmtProp (sub_prop)) <= pcnt) |]
  &&  emp
.

Definition prop2cnf_which_implies_wit_10 := 
forall (data_pre: Z) (clist'': (@list (@list Z))) (pcnt'': Z) (ccnt'': Z) ,
  (store_predata data_pre clist'' pcnt'' ccnt'' )
|--
  EX (y'': Z) ,
  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist'')) = ccnt'') |] 
  &&  [| ((prop_cnt_inf (clist'')) <= pcnt'') |] 
  &&  [| (pcnt'' >= 0) |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y'')
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> pcnt'')
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt'')
  **  (sll_cnf_list y'' clist'' )
.

Definition prop2cnf_which_implies_wit_11 := 
forall (pcnt'': Z) (res: Z) ,
  [| (pcnt'' >= 0) |] 
  &&  [| (res = (pcnt'' + 1 )) |]
  &&  emp
|--
  [| (res <> 0) |]
  &&  emp
.

Definition prop2cnf_which_implies_wit_12 := 
forall (data_pre: Z) (clist'': (@list (@list Z))) (pcnt'': Z) (ccnt'': Z) (y'': Z) ,
  [| (data_pre <> 0) |] 
  &&  [| ((Zlength (clist'')) = ccnt'') |] 
  &&  [| ((prop_cnt_inf (clist'')) <= pcnt'') |]
  &&  ((&((data_pre)  # "PreData" ->ₛ "cnf_res")) # Ptr  |-> y'')
  **  ((&((data_pre)  # "PreData" ->ₛ "prop_cnt")) # Int  |-> (pcnt'' + 1 ))
  **  ((&((data_pre)  # "PreData" ->ₛ "clause_cnt")) # Int  |-> ccnt'')
  **  (sll_cnf_list y'' clist'' )
|--
  (store_predata data_pre clist'' (pcnt'' + 1 ) ccnt'' )
.

Definition prop2cnf_which_implies_wit_13 := 
forall (clist'': (@list (@list Z))) (pcnt'': Z) ,
  [| ((prop_cnt_inf (clist'')) <= pcnt'') |]
  &&  emp
|--
  [| (((prop_cnt_inf (clist'')) + 1 ) <= (pcnt'' + 1 )) |]
  &&  emp
.

Definition prop2cnf_which_implies_wit_14 := 
forall (p_pre: Z) (prop: smt_prop) (p_pre_type: Z) (p: Z) ,
  [| (p_pre_type = 7) |] 
  &&  [| (p_pre_type = (SmtPTID (prop))) |]
  &&  ((&((p_pre)  # "SmtProp" ->ₛ "type")) # Int  |-> p_pre_type)
  **  (store_SmtProp' p prop )
|--
  EX (var: Z) ,
  [| (prop = (SmtV (var))) |] 
  &&  [| (var <> 0) |] 
  &&  [| (p_pre <> 0) |]
  &&  ((&((p)  # "SmtProp" ->ₛ "prop" .ₛ "Propvar")) # Int  |-> var)
  **  ((&((p)  # "SmtProp" ->ₛ "type")) # Int  |-> (SmtPTID (prop)))
.

Module Type VC_Correct.

Axiom proof_of_clause_gen_unary_safety_wit_1 : clause_gen_unary_safety_wit_1.
Axiom proof_of_clause_gen_unary_safety_wit_2 : clause_gen_unary_safety_wit_2.
Axiom proof_of_clause_gen_unary_safety_wit_3 : clause_gen_unary_safety_wit_3.
Axiom proof_of_clause_gen_unary_safety_wit_4 : clause_gen_unary_safety_wit_4.
Axiom proof_of_clause_gen_unary_safety_wit_5 : clause_gen_unary_safety_wit_5.
Axiom proof_of_clause_gen_unary_safety_wit_6 : clause_gen_unary_safety_wit_6.
Axiom proof_of_clause_gen_unary_safety_wit_7 : clause_gen_unary_safety_wit_7.
Axiom proof_of_clause_gen_unary_safety_wit_8 : clause_gen_unary_safety_wit_8.
Axiom proof_of_clause_gen_unary_safety_wit_9 : clause_gen_unary_safety_wit_9.
Axiom proof_of_clause_gen_unary_return_wit_1 : clause_gen_unary_return_wit_1.
Axiom proof_of_clause_gen_unary_partial_solve_wit_1_pure : clause_gen_unary_partial_solve_wit_1_pure.
Axiom proof_of_clause_gen_unary_partial_solve_wit_1 : clause_gen_unary_partial_solve_wit_1.
Axiom proof_of_clause_gen_unary_partial_solve_wit_2_pure : clause_gen_unary_partial_solve_wit_2_pure.
Axiom proof_of_clause_gen_unary_partial_solve_wit_2 : clause_gen_unary_partial_solve_wit_2.
Axiom proof_of_clause_gen_unary_partial_solve_wit_3 : clause_gen_unary_partial_solve_wit_3.
Axiom proof_of_clause_gen_unary_partial_solve_wit_4 : clause_gen_unary_partial_solve_wit_4.
Axiom proof_of_clause_gen_unary_partial_solve_wit_5 : clause_gen_unary_partial_solve_wit_5.
Axiom proof_of_clause_gen_unary_partial_solve_wit_6 : clause_gen_unary_partial_solve_wit_6.
Axiom proof_of_clause_gen_unary_partial_solve_wit_7 : clause_gen_unary_partial_solve_wit_7.
Axiom proof_of_clause_gen_unary_partial_solve_wit_8 : clause_gen_unary_partial_solve_wit_8.
Axiom proof_of_clause_gen_unary_partial_solve_wit_9 : clause_gen_unary_partial_solve_wit_9.
Axiom proof_of_clause_gen_unary_which_implies_wit_1 : clause_gen_unary_which_implies_wit_1.
Axiom proof_of_clause_gen_binary_safety_wit_1 : clause_gen_binary_safety_wit_1.
Axiom proof_of_clause_gen_binary_safety_wit_2 : clause_gen_binary_safety_wit_2.
Axiom proof_of_clause_gen_binary_safety_wit_3 : clause_gen_binary_safety_wit_3.
Axiom proof_of_clause_gen_binary_safety_wit_4 : clause_gen_binary_safety_wit_4.
Axiom proof_of_clause_gen_binary_safety_wit_5 : clause_gen_binary_safety_wit_5.
Axiom proof_of_clause_gen_binary_safety_wit_6 : clause_gen_binary_safety_wit_6.
Axiom proof_of_clause_gen_binary_safety_wit_7 : clause_gen_binary_safety_wit_7.
Axiom proof_of_clause_gen_binary_safety_wit_8 : clause_gen_binary_safety_wit_8.
Axiom proof_of_clause_gen_binary_safety_wit_9 : clause_gen_binary_safety_wit_9.
Axiom proof_of_clause_gen_binary_safety_wit_10 : clause_gen_binary_safety_wit_10.
Axiom proof_of_clause_gen_binary_safety_wit_11 : clause_gen_binary_safety_wit_11.
Axiom proof_of_clause_gen_binary_safety_wit_12 : clause_gen_binary_safety_wit_12.
Axiom proof_of_clause_gen_binary_safety_wit_13 : clause_gen_binary_safety_wit_13.
Axiom proof_of_clause_gen_binary_safety_wit_14 : clause_gen_binary_safety_wit_14.
Axiom proof_of_clause_gen_binary_safety_wit_15 : clause_gen_binary_safety_wit_15.
Axiom proof_of_clause_gen_binary_safety_wit_16 : clause_gen_binary_safety_wit_16.
Axiom proof_of_clause_gen_binary_safety_wit_17 : clause_gen_binary_safety_wit_17.
Axiom proof_of_clause_gen_binary_safety_wit_18 : clause_gen_binary_safety_wit_18.
Axiom proof_of_clause_gen_binary_safety_wit_19 : clause_gen_binary_safety_wit_19.
Axiom proof_of_clause_gen_binary_safety_wit_20 : clause_gen_binary_safety_wit_20.
Axiom proof_of_clause_gen_binary_safety_wit_21 : clause_gen_binary_safety_wit_21.
Axiom proof_of_clause_gen_binary_safety_wit_22 : clause_gen_binary_safety_wit_22.
Axiom proof_of_clause_gen_binary_safety_wit_23 : clause_gen_binary_safety_wit_23.
Axiom proof_of_clause_gen_binary_safety_wit_24 : clause_gen_binary_safety_wit_24.
Axiom proof_of_clause_gen_binary_safety_wit_25 : clause_gen_binary_safety_wit_25.
Axiom proof_of_clause_gen_binary_safety_wit_26 : clause_gen_binary_safety_wit_26.
Axiom proof_of_clause_gen_binary_safety_wit_27 : clause_gen_binary_safety_wit_27.
Axiom proof_of_clause_gen_binary_safety_wit_28 : clause_gen_binary_safety_wit_28.
Axiom proof_of_clause_gen_binary_safety_wit_29 : clause_gen_binary_safety_wit_29.
Axiom proof_of_clause_gen_binary_safety_wit_30 : clause_gen_binary_safety_wit_30.
Axiom proof_of_clause_gen_binary_safety_wit_31 : clause_gen_binary_safety_wit_31.
Axiom proof_of_clause_gen_binary_safety_wit_32 : clause_gen_binary_safety_wit_32.
Axiom proof_of_clause_gen_binary_safety_wit_33 : clause_gen_binary_safety_wit_33.
Axiom proof_of_clause_gen_binary_safety_wit_34 : clause_gen_binary_safety_wit_34.
Axiom proof_of_clause_gen_binary_safety_wit_35 : clause_gen_binary_safety_wit_35.
Axiom proof_of_clause_gen_binary_safety_wit_36 : clause_gen_binary_safety_wit_36.
Axiom proof_of_clause_gen_binary_safety_wit_37 : clause_gen_binary_safety_wit_37.
Axiom proof_of_clause_gen_binary_safety_wit_38 : clause_gen_binary_safety_wit_38.
Axiom proof_of_clause_gen_binary_safety_wit_39 : clause_gen_binary_safety_wit_39.
Axiom proof_of_clause_gen_binary_safety_wit_40 : clause_gen_binary_safety_wit_40.
Axiom proof_of_clause_gen_binary_safety_wit_41 : clause_gen_binary_safety_wit_41.
Axiom proof_of_clause_gen_binary_safety_wit_42 : clause_gen_binary_safety_wit_42.
Axiom proof_of_clause_gen_binary_safety_wit_43 : clause_gen_binary_safety_wit_43.
Axiom proof_of_clause_gen_binary_safety_wit_44 : clause_gen_binary_safety_wit_44.
Axiom proof_of_clause_gen_binary_safety_wit_45 : clause_gen_binary_safety_wit_45.
Axiom proof_of_clause_gen_binary_safety_wit_46 : clause_gen_binary_safety_wit_46.
Axiom proof_of_clause_gen_binary_safety_wit_47 : clause_gen_binary_safety_wit_47.
Axiom proof_of_clause_gen_binary_safety_wit_48 : clause_gen_binary_safety_wit_48.
Axiom proof_of_clause_gen_binary_safety_wit_49 : clause_gen_binary_safety_wit_49.
Axiom proof_of_clause_gen_binary_safety_wit_50 : clause_gen_binary_safety_wit_50.
Axiom proof_of_clause_gen_binary_safety_wit_51 : clause_gen_binary_safety_wit_51.
Axiom proof_of_clause_gen_binary_safety_wit_52 : clause_gen_binary_safety_wit_52.
Axiom proof_of_clause_gen_binary_safety_wit_53 : clause_gen_binary_safety_wit_53.
Axiom proof_of_clause_gen_binary_safety_wit_54 : clause_gen_binary_safety_wit_54.
Axiom proof_of_clause_gen_binary_safety_wit_55 : clause_gen_binary_safety_wit_55.
Axiom proof_of_clause_gen_binary_safety_wit_56 : clause_gen_binary_safety_wit_56.
Axiom proof_of_clause_gen_binary_safety_wit_57 : clause_gen_binary_safety_wit_57.
Axiom proof_of_clause_gen_binary_safety_wit_58 : clause_gen_binary_safety_wit_58.
Axiom proof_of_clause_gen_binary_safety_wit_59 : clause_gen_binary_safety_wit_59.
Axiom proof_of_clause_gen_binary_safety_wit_60 : clause_gen_binary_safety_wit_60.
Axiom proof_of_clause_gen_binary_safety_wit_61 : clause_gen_binary_safety_wit_61.
Axiom proof_of_clause_gen_binary_safety_wit_62 : clause_gen_binary_safety_wit_62.
Axiom proof_of_clause_gen_binary_safety_wit_63 : clause_gen_binary_safety_wit_63.
Axiom proof_of_clause_gen_binary_safety_wit_64 : clause_gen_binary_safety_wit_64.
Axiom proof_of_clause_gen_binary_safety_wit_65 : clause_gen_binary_safety_wit_65.
Axiom proof_of_clause_gen_binary_safety_wit_66 : clause_gen_binary_safety_wit_66.
Axiom proof_of_clause_gen_binary_safety_wit_67 : clause_gen_binary_safety_wit_67.
Axiom proof_of_clause_gen_binary_safety_wit_68 : clause_gen_binary_safety_wit_68.
Axiom proof_of_clause_gen_binary_safety_wit_69 : clause_gen_binary_safety_wit_69.
Axiom proof_of_clause_gen_binary_safety_wit_70 : clause_gen_binary_safety_wit_70.
Axiom proof_of_clause_gen_binary_safety_wit_71 : clause_gen_binary_safety_wit_71.
Axiom proof_of_clause_gen_binary_safety_wit_72 : clause_gen_binary_safety_wit_72.
Axiom proof_of_clause_gen_binary_safety_wit_73 : clause_gen_binary_safety_wit_73.
Axiom proof_of_clause_gen_binary_safety_wit_74 : clause_gen_binary_safety_wit_74.
Axiom proof_of_clause_gen_binary_safety_wit_75 : clause_gen_binary_safety_wit_75.
Axiom proof_of_clause_gen_binary_safety_wit_76 : clause_gen_binary_safety_wit_76.
Axiom proof_of_clause_gen_binary_safety_wit_77 : clause_gen_binary_safety_wit_77.
Axiom proof_of_clause_gen_binary_safety_wit_78 : clause_gen_binary_safety_wit_78.
Axiom proof_of_clause_gen_binary_safety_wit_79 : clause_gen_binary_safety_wit_79.
Axiom proof_of_clause_gen_binary_safety_wit_80 : clause_gen_binary_safety_wit_80.
Axiom proof_of_clause_gen_binary_safety_wit_81 : clause_gen_binary_safety_wit_81.
Axiom proof_of_clause_gen_binary_safety_wit_82 : clause_gen_binary_safety_wit_82.
Axiom proof_of_clause_gen_binary_safety_wit_83 : clause_gen_binary_safety_wit_83.
Axiom proof_of_clause_gen_binary_safety_wit_84 : clause_gen_binary_safety_wit_84.
Axiom proof_of_clause_gen_binary_safety_wit_85 : clause_gen_binary_safety_wit_85.
Axiom proof_of_clause_gen_binary_safety_wit_86 : clause_gen_binary_safety_wit_86.
Axiom proof_of_clause_gen_binary_safety_wit_87 : clause_gen_binary_safety_wit_87.
Axiom proof_of_clause_gen_binary_safety_wit_88 : clause_gen_binary_safety_wit_88.
Axiom proof_of_clause_gen_binary_safety_wit_89 : clause_gen_binary_safety_wit_89.
Axiom proof_of_clause_gen_binary_safety_wit_90 : clause_gen_binary_safety_wit_90.
Axiom proof_of_clause_gen_binary_safety_wit_91 : clause_gen_binary_safety_wit_91.
Axiom proof_of_clause_gen_binary_safety_wit_92 : clause_gen_binary_safety_wit_92.
Axiom proof_of_clause_gen_binary_safety_wit_93 : clause_gen_binary_safety_wit_93.
Axiom proof_of_clause_gen_binary_safety_wit_94 : clause_gen_binary_safety_wit_94.
Axiom proof_of_clause_gen_binary_safety_wit_95 : clause_gen_binary_safety_wit_95.
Axiom proof_of_clause_gen_binary_safety_wit_96 : clause_gen_binary_safety_wit_96.
Axiom proof_of_clause_gen_binary_safety_wit_97 : clause_gen_binary_safety_wit_97.
Axiom proof_of_clause_gen_binary_safety_wit_98 : clause_gen_binary_safety_wit_98.
Axiom proof_of_clause_gen_binary_safety_wit_99 : clause_gen_binary_safety_wit_99.
Axiom proof_of_clause_gen_binary_safety_wit_100 : clause_gen_binary_safety_wit_100.
Axiom proof_of_clause_gen_binary_safety_wit_101 : clause_gen_binary_safety_wit_101.
Axiom proof_of_clause_gen_binary_safety_wit_102 : clause_gen_binary_safety_wit_102.
Axiom proof_of_clause_gen_binary_safety_wit_103 : clause_gen_binary_safety_wit_103.
Axiom proof_of_clause_gen_binary_safety_wit_104 : clause_gen_binary_safety_wit_104.
Axiom proof_of_clause_gen_binary_safety_wit_105 : clause_gen_binary_safety_wit_105.
Axiom proof_of_clause_gen_binary_safety_wit_106 : clause_gen_binary_safety_wit_106.
Axiom proof_of_clause_gen_binary_safety_wit_107 : clause_gen_binary_safety_wit_107.
Axiom proof_of_clause_gen_binary_safety_wit_108 : clause_gen_binary_safety_wit_108.
Axiom proof_of_clause_gen_binary_safety_wit_109 : clause_gen_binary_safety_wit_109.
Axiom proof_of_clause_gen_binary_safety_wit_110 : clause_gen_binary_safety_wit_110.
Axiom proof_of_clause_gen_binary_safety_wit_111 : clause_gen_binary_safety_wit_111.
Axiom proof_of_clause_gen_binary_safety_wit_112 : clause_gen_binary_safety_wit_112.
Axiom proof_of_clause_gen_binary_safety_wit_113 : clause_gen_binary_safety_wit_113.
Axiom proof_of_clause_gen_binary_safety_wit_114 : clause_gen_binary_safety_wit_114.
Axiom proof_of_clause_gen_binary_safety_wit_115 : clause_gen_binary_safety_wit_115.
Axiom proof_of_clause_gen_binary_safety_wit_116 : clause_gen_binary_safety_wit_116.
Axiom proof_of_clause_gen_binary_safety_wit_117 : clause_gen_binary_safety_wit_117.
Axiom proof_of_clause_gen_binary_safety_wit_118 : clause_gen_binary_safety_wit_118.
Axiom proof_of_clause_gen_binary_safety_wit_119 : clause_gen_binary_safety_wit_119.
Axiom proof_of_clause_gen_binary_safety_wit_120 : clause_gen_binary_safety_wit_120.
Axiom proof_of_clause_gen_binary_safety_wit_121 : clause_gen_binary_safety_wit_121.
Axiom proof_of_clause_gen_binary_safety_wit_122 : clause_gen_binary_safety_wit_122.
Axiom proof_of_clause_gen_binary_safety_wit_123 : clause_gen_binary_safety_wit_123.
Axiom proof_of_clause_gen_binary_safety_wit_124 : clause_gen_binary_safety_wit_124.
Axiom proof_of_clause_gen_binary_safety_wit_125 : clause_gen_binary_safety_wit_125.
Axiom proof_of_clause_gen_binary_safety_wit_126 : clause_gen_binary_safety_wit_126.
Axiom proof_of_clause_gen_binary_safety_wit_127 : clause_gen_binary_safety_wit_127.
Axiom proof_of_clause_gen_binary_safety_wit_128 : clause_gen_binary_safety_wit_128.
Axiom proof_of_clause_gen_binary_safety_wit_129 : clause_gen_binary_safety_wit_129.
Axiom proof_of_clause_gen_binary_safety_wit_130 : clause_gen_binary_safety_wit_130.
Axiom proof_of_clause_gen_binary_safety_wit_131 : clause_gen_binary_safety_wit_131.
Axiom proof_of_clause_gen_binary_safety_wit_132 : clause_gen_binary_safety_wit_132.
Axiom proof_of_clause_gen_binary_safety_wit_133 : clause_gen_binary_safety_wit_133.
Axiom proof_of_clause_gen_binary_safety_wit_134 : clause_gen_binary_safety_wit_134.
Axiom proof_of_clause_gen_binary_safety_wit_135 : clause_gen_binary_safety_wit_135.
Axiom proof_of_clause_gen_binary_safety_wit_136 : clause_gen_binary_safety_wit_136.
Axiom proof_of_clause_gen_binary_return_wit_1_1 : clause_gen_binary_return_wit_1_1.
Axiom proof_of_clause_gen_binary_return_wit_1_2 : clause_gen_binary_return_wit_1_2.
Axiom proof_of_clause_gen_binary_return_wit_1_3 : clause_gen_binary_return_wit_1_3.
Axiom proof_of_clause_gen_binary_return_wit_1_4 : clause_gen_binary_return_wit_1_4.
Axiom proof_of_clause_gen_binary_return_wit_1_5 : clause_gen_binary_return_wit_1_5.
Axiom proof_of_clause_gen_binary_return_wit_1_6 : clause_gen_binary_return_wit_1_6.
Axiom proof_of_clause_gen_binary_return_wit_1_7 : clause_gen_binary_return_wit_1_7.
Axiom proof_of_clause_gen_binary_return_wit_1_8 : clause_gen_binary_return_wit_1_8.
Axiom proof_of_clause_gen_binary_partial_solve_wit_1_pure : clause_gen_binary_partial_solve_wit_1_pure.
Axiom proof_of_clause_gen_binary_partial_solve_wit_1 : clause_gen_binary_partial_solve_wit_1.
Axiom proof_of_clause_gen_binary_partial_solve_wit_2_pure : clause_gen_binary_partial_solve_wit_2_pure.
Axiom proof_of_clause_gen_binary_partial_solve_wit_2 : clause_gen_binary_partial_solve_wit_2.
Axiom proof_of_clause_gen_binary_partial_solve_wit_3_pure : clause_gen_binary_partial_solve_wit_3_pure.
Axiom proof_of_clause_gen_binary_partial_solve_wit_3 : clause_gen_binary_partial_solve_wit_3.
Axiom proof_of_clause_gen_binary_partial_solve_wit_4_pure : clause_gen_binary_partial_solve_wit_4_pure.
Axiom proof_of_clause_gen_binary_partial_solve_wit_4 : clause_gen_binary_partial_solve_wit_4.
Axiom proof_of_clause_gen_binary_partial_solve_wit_5 : clause_gen_binary_partial_solve_wit_5.
Axiom proof_of_clause_gen_binary_partial_solve_wit_6 : clause_gen_binary_partial_solve_wit_6.
Axiom proof_of_clause_gen_binary_partial_solve_wit_7 : clause_gen_binary_partial_solve_wit_7.
Axiom proof_of_clause_gen_binary_partial_solve_wit_8 : clause_gen_binary_partial_solve_wit_8.
Axiom proof_of_clause_gen_binary_partial_solve_wit_9 : clause_gen_binary_partial_solve_wit_9.
Axiom proof_of_clause_gen_binary_partial_solve_wit_10 : clause_gen_binary_partial_solve_wit_10.
Axiom proof_of_clause_gen_binary_partial_solve_wit_11 : clause_gen_binary_partial_solve_wit_11.
Axiom proof_of_clause_gen_binary_partial_solve_wit_12 : clause_gen_binary_partial_solve_wit_12.
Axiom proof_of_clause_gen_binary_partial_solve_wit_13 : clause_gen_binary_partial_solve_wit_13.
Axiom proof_of_clause_gen_binary_partial_solve_wit_14 : clause_gen_binary_partial_solve_wit_14.
Axiom proof_of_clause_gen_binary_partial_solve_wit_15 : clause_gen_binary_partial_solve_wit_15.
Axiom proof_of_clause_gen_binary_partial_solve_wit_16 : clause_gen_binary_partial_solve_wit_16.
Axiom proof_of_clause_gen_binary_partial_solve_wit_17 : clause_gen_binary_partial_solve_wit_17.
Axiom proof_of_clause_gen_binary_partial_solve_wit_18 : clause_gen_binary_partial_solve_wit_18.
Axiom proof_of_clause_gen_binary_partial_solve_wit_19 : clause_gen_binary_partial_solve_wit_19.
Axiom proof_of_clause_gen_binary_partial_solve_wit_20 : clause_gen_binary_partial_solve_wit_20.
Axiom proof_of_clause_gen_binary_partial_solve_wit_21 : clause_gen_binary_partial_solve_wit_21.
Axiom proof_of_clause_gen_binary_partial_solve_wit_22 : clause_gen_binary_partial_solve_wit_22.
Axiom proof_of_clause_gen_binary_partial_solve_wit_23 : clause_gen_binary_partial_solve_wit_23.
Axiom proof_of_clause_gen_binary_partial_solve_wit_24 : clause_gen_binary_partial_solve_wit_24.
Axiom proof_of_clause_gen_binary_partial_solve_wit_25 : clause_gen_binary_partial_solve_wit_25.
Axiom proof_of_clause_gen_binary_partial_solve_wit_26 : clause_gen_binary_partial_solve_wit_26.
Axiom proof_of_clause_gen_binary_partial_solve_wit_27 : clause_gen_binary_partial_solve_wit_27.
Axiom proof_of_clause_gen_binary_partial_solve_wit_28 : clause_gen_binary_partial_solve_wit_28.
Axiom proof_of_clause_gen_binary_partial_solve_wit_29 : clause_gen_binary_partial_solve_wit_29.
Axiom proof_of_clause_gen_binary_partial_solve_wit_30 : clause_gen_binary_partial_solve_wit_30.
Axiom proof_of_clause_gen_binary_partial_solve_wit_31 : clause_gen_binary_partial_solve_wit_31.
Axiom proof_of_clause_gen_binary_partial_solve_wit_32 : clause_gen_binary_partial_solve_wit_32.
Axiom proof_of_clause_gen_binary_partial_solve_wit_33 : clause_gen_binary_partial_solve_wit_33.
Axiom proof_of_clause_gen_binary_partial_solve_wit_34 : clause_gen_binary_partial_solve_wit_34.
Axiom proof_of_clause_gen_binary_partial_solve_wit_35 : clause_gen_binary_partial_solve_wit_35.
Axiom proof_of_clause_gen_binary_partial_solve_wit_36 : clause_gen_binary_partial_solve_wit_36.
Axiom proof_of_clause_gen_binary_partial_solve_wit_37 : clause_gen_binary_partial_solve_wit_37.
Axiom proof_of_clause_gen_binary_partial_solve_wit_38 : clause_gen_binary_partial_solve_wit_38.
Axiom proof_of_clause_gen_binary_partial_solve_wit_39 : clause_gen_binary_partial_solve_wit_39.
Axiom proof_of_clause_gen_binary_partial_solve_wit_40 : clause_gen_binary_partial_solve_wit_40.
Axiom proof_of_clause_gen_binary_partial_solve_wit_41 : clause_gen_binary_partial_solve_wit_41.
Axiom proof_of_clause_gen_binary_partial_solve_wit_42 : clause_gen_binary_partial_solve_wit_42.
Axiom proof_of_clause_gen_binary_partial_solve_wit_43 : clause_gen_binary_partial_solve_wit_43.
Axiom proof_of_clause_gen_binary_partial_solve_wit_44 : clause_gen_binary_partial_solve_wit_44.
Axiom proof_of_clause_gen_binary_partial_solve_wit_45 : clause_gen_binary_partial_solve_wit_45.
Axiom proof_of_clause_gen_binary_partial_solve_wit_46 : clause_gen_binary_partial_solve_wit_46.
Axiom proof_of_clause_gen_binary_partial_solve_wit_47 : clause_gen_binary_partial_solve_wit_47.
Axiom proof_of_clause_gen_binary_partial_solve_wit_48 : clause_gen_binary_partial_solve_wit_48.
Axiom proof_of_clause_gen_binary_partial_solve_wit_49 : clause_gen_binary_partial_solve_wit_49.
Axiom proof_of_clause_gen_binary_partial_solve_wit_50 : clause_gen_binary_partial_solve_wit_50.
Axiom proof_of_clause_gen_binary_partial_solve_wit_51 : clause_gen_binary_partial_solve_wit_51.
Axiom proof_of_clause_gen_binary_partial_solve_wit_52 : clause_gen_binary_partial_solve_wit_52.
Axiom proof_of_clause_gen_binary_partial_solve_wit_53 : clause_gen_binary_partial_solve_wit_53.
Axiom proof_of_clause_gen_binary_partial_solve_wit_54 : clause_gen_binary_partial_solve_wit_54.
Axiom proof_of_clause_gen_binary_partial_solve_wit_55 : clause_gen_binary_partial_solve_wit_55.
Axiom proof_of_clause_gen_binary_partial_solve_wit_56 : clause_gen_binary_partial_solve_wit_56.
Axiom proof_of_clause_gen_binary_partial_solve_wit_57 : clause_gen_binary_partial_solve_wit_57.
Axiom proof_of_clause_gen_binary_partial_solve_wit_58 : clause_gen_binary_partial_solve_wit_58.
Axiom proof_of_clause_gen_binary_partial_solve_wit_59 : clause_gen_binary_partial_solve_wit_59.
Axiom proof_of_clause_gen_binary_partial_solve_wit_60 : clause_gen_binary_partial_solve_wit_60.
Axiom proof_of_clause_gen_binary_partial_solve_wit_61 : clause_gen_binary_partial_solve_wit_61.
Axiom proof_of_clause_gen_binary_partial_solve_wit_62 : clause_gen_binary_partial_solve_wit_62.
Axiom proof_of_clause_gen_binary_partial_solve_wit_63 : clause_gen_binary_partial_solve_wit_63.
Axiom proof_of_clause_gen_binary_partial_solve_wit_64 : clause_gen_binary_partial_solve_wit_64.
Axiom proof_of_clause_gen_binary_partial_solve_wit_65 : clause_gen_binary_partial_solve_wit_65.
Axiom proof_of_clause_gen_binary_partial_solve_wit_66 : clause_gen_binary_partial_solve_wit_66.
Axiom proof_of_clause_gen_binary_partial_solve_wit_67 : clause_gen_binary_partial_solve_wit_67.
Axiom proof_of_clause_gen_binary_partial_solve_wit_68 : clause_gen_binary_partial_solve_wit_68.
Axiom proof_of_clause_gen_binary_partial_solve_wit_69 : clause_gen_binary_partial_solve_wit_69.
Axiom proof_of_clause_gen_binary_partial_solve_wit_70 : clause_gen_binary_partial_solve_wit_70.
Axiom proof_of_clause_gen_binary_partial_solve_wit_71 : clause_gen_binary_partial_solve_wit_71.
Axiom proof_of_clause_gen_binary_partial_solve_wit_72 : clause_gen_binary_partial_solve_wit_72.
Axiom proof_of_clause_gen_binary_partial_solve_wit_73 : clause_gen_binary_partial_solve_wit_73.
Axiom proof_of_clause_gen_binary_partial_solve_wit_74 : clause_gen_binary_partial_solve_wit_74.
Axiom proof_of_clause_gen_binary_partial_solve_wit_75 : clause_gen_binary_partial_solve_wit_75.
Axiom proof_of_clause_gen_binary_partial_solve_wit_76 : clause_gen_binary_partial_solve_wit_76.
Axiom proof_of_clause_gen_binary_partial_solve_wit_77 : clause_gen_binary_partial_solve_wit_77.
Axiom proof_of_clause_gen_binary_partial_solve_wit_78 : clause_gen_binary_partial_solve_wit_78.
Axiom proof_of_clause_gen_binary_partial_solve_wit_79 : clause_gen_binary_partial_solve_wit_79.
Axiom proof_of_clause_gen_binary_partial_solve_wit_80 : clause_gen_binary_partial_solve_wit_80.
Axiom proof_of_clause_gen_binary_partial_solve_wit_81 : clause_gen_binary_partial_solve_wit_81.
Axiom proof_of_clause_gen_binary_partial_solve_wit_82 : clause_gen_binary_partial_solve_wit_82.
Axiom proof_of_clause_gen_binary_partial_solve_wit_83 : clause_gen_binary_partial_solve_wit_83.
Axiom proof_of_clause_gen_binary_partial_solve_wit_84_pure : clause_gen_binary_partial_solve_wit_84_pure.
Axiom proof_of_clause_gen_binary_partial_solve_wit_84 : clause_gen_binary_partial_solve_wit_84.
Axiom proof_of_clause_gen_binary_partial_solve_wit_85_pure : clause_gen_binary_partial_solve_wit_85_pure.
Axiom proof_of_clause_gen_binary_partial_solve_wit_85 : clause_gen_binary_partial_solve_wit_85.
Axiom proof_of_clause_gen_binary_partial_solve_wit_86_pure : clause_gen_binary_partial_solve_wit_86_pure.
Axiom proof_of_clause_gen_binary_partial_solve_wit_86 : clause_gen_binary_partial_solve_wit_86.
Axiom proof_of_clause_gen_binary_partial_solve_wit_87_pure : clause_gen_binary_partial_solve_wit_87_pure.
Axiom proof_of_clause_gen_binary_partial_solve_wit_87 : clause_gen_binary_partial_solve_wit_87.
Axiom proof_of_clause_gen_binary_partial_solve_wit_88_pure : clause_gen_binary_partial_solve_wit_88_pure.
Axiom proof_of_clause_gen_binary_partial_solve_wit_88 : clause_gen_binary_partial_solve_wit_88.
Axiom proof_of_clause_gen_binary_partial_solve_wit_89_pure : clause_gen_binary_partial_solve_wit_89_pure.
Axiom proof_of_clause_gen_binary_partial_solve_wit_89 : clause_gen_binary_partial_solve_wit_89.
Axiom proof_of_clause_gen_binary_partial_solve_wit_90_pure : clause_gen_binary_partial_solve_wit_90_pure.
Axiom proof_of_clause_gen_binary_partial_solve_wit_90 : clause_gen_binary_partial_solve_wit_90.
Axiom proof_of_clause_gen_binary_partial_solve_wit_91_pure : clause_gen_binary_partial_solve_wit_91_pure.
Axiom proof_of_clause_gen_binary_partial_solve_wit_91 : clause_gen_binary_partial_solve_wit_91.
Axiom proof_of_clause_gen_binary_partial_solve_wit_92_pure : clause_gen_binary_partial_solve_wit_92_pure.
Axiom proof_of_clause_gen_binary_partial_solve_wit_92 : clause_gen_binary_partial_solve_wit_92.
Axiom proof_of_clause_gen_binary_partial_solve_wit_93_pure : clause_gen_binary_partial_solve_wit_93_pure.
Axiom proof_of_clause_gen_binary_partial_solve_wit_93 : clause_gen_binary_partial_solve_wit_93.
Axiom proof_of_clause_gen_binary_partial_solve_wit_94_pure : clause_gen_binary_partial_solve_wit_94_pure.
Axiom proof_of_clause_gen_binary_partial_solve_wit_94 : clause_gen_binary_partial_solve_wit_94.
Axiom proof_of_clause_gen_binary_partial_solve_wit_95_pure : clause_gen_binary_partial_solve_wit_95_pure.
Axiom proof_of_clause_gen_binary_partial_solve_wit_95 : clause_gen_binary_partial_solve_wit_95.
Axiom proof_of_clause_gen_binary_partial_solve_wit_96_pure : clause_gen_binary_partial_solve_wit_96_pure.
Axiom proof_of_clause_gen_binary_partial_solve_wit_96 : clause_gen_binary_partial_solve_wit_96.
Axiom proof_of_clause_gen_binary_partial_solve_wit_97_pure : clause_gen_binary_partial_solve_wit_97_pure.
Axiom proof_of_clause_gen_binary_partial_solve_wit_97 : clause_gen_binary_partial_solve_wit_97.
Axiom proof_of_clause_gen_binary_partial_solve_wit_98_pure : clause_gen_binary_partial_solve_wit_98_pure.
Axiom proof_of_clause_gen_binary_partial_solve_wit_98 : clause_gen_binary_partial_solve_wit_98.
Axiom proof_of_clause_gen_binary_partial_solve_wit_99_pure : clause_gen_binary_partial_solve_wit_99_pure.
Axiom proof_of_clause_gen_binary_partial_solve_wit_99 : clause_gen_binary_partial_solve_wit_99.
Axiom proof_of_clause_gen_binary_partial_solve_wit_100_pure : clause_gen_binary_partial_solve_wit_100_pure.
Axiom proof_of_clause_gen_binary_partial_solve_wit_100 : clause_gen_binary_partial_solve_wit_100.
Axiom proof_of_clause_gen_binary_partial_solve_wit_101_pure : clause_gen_binary_partial_solve_wit_101_pure.
Axiom proof_of_clause_gen_binary_partial_solve_wit_101 : clause_gen_binary_partial_solve_wit_101.
Axiom proof_of_clause_gen_binary_partial_solve_wit_102_pure : clause_gen_binary_partial_solve_wit_102_pure.
Axiom proof_of_clause_gen_binary_partial_solve_wit_102 : clause_gen_binary_partial_solve_wit_102.
Axiom proof_of_clause_gen_binary_partial_solve_wit_103_pure : clause_gen_binary_partial_solve_wit_103_pure.
Axiom proof_of_clause_gen_binary_partial_solve_wit_103 : clause_gen_binary_partial_solve_wit_103.
Axiom proof_of_clause_gen_binary_partial_solve_wit_104_pure : clause_gen_binary_partial_solve_wit_104_pure.
Axiom proof_of_clause_gen_binary_partial_solve_wit_104 : clause_gen_binary_partial_solve_wit_104.
Axiom proof_of_clause_gen_binary_partial_solve_wit_105_pure : clause_gen_binary_partial_solve_wit_105_pure.
Axiom proof_of_clause_gen_binary_partial_solve_wit_105 : clause_gen_binary_partial_solve_wit_105.
Axiom proof_of_clause_gen_binary_which_implies_wit_1 : clause_gen_binary_which_implies_wit_1.
Axiom proof_of_prop2cnf_safety_wit_1 : prop2cnf_safety_wit_1.
Axiom proof_of_prop2cnf_safety_wit_2 : prop2cnf_safety_wit_2.
Axiom proof_of_prop2cnf_safety_wit_3 : prop2cnf_safety_wit_3.
Axiom proof_of_prop2cnf_safety_wit_4 : prop2cnf_safety_wit_4.
Axiom proof_of_prop2cnf_safety_wit_5 : prop2cnf_safety_wit_5.
Axiom proof_of_prop2cnf_safety_wit_6 : prop2cnf_safety_wit_6.
Axiom proof_of_prop2cnf_safety_wit_7 : prop2cnf_safety_wit_7.
Axiom proof_of_prop2cnf_safety_wit_8 : prop2cnf_safety_wit_8.
Axiom proof_of_prop2cnf_safety_wit_9 : prop2cnf_safety_wit_9.
Axiom proof_of_prop2cnf_entail_wit_1 : prop2cnf_entail_wit_1.
Axiom proof_of_prop2cnf_entail_wit_2 : prop2cnf_entail_wit_2.
Axiom proof_of_prop2cnf_return_wit_1_1 : prop2cnf_return_wit_1_1.
Axiom proof_of_prop2cnf_return_wit_1_2 : prop2cnf_return_wit_1_2.
Axiom proof_of_prop2cnf_return_wit_1_3 : prop2cnf_return_wit_1_3.
Axiom proof_of_prop2cnf_partial_solve_wit_1 : prop2cnf_partial_solve_wit_1.
Axiom proof_of_prop2cnf_partial_solve_wit_2_pure : prop2cnf_partial_solve_wit_2_pure.
Axiom proof_of_prop2cnf_partial_solve_wit_2 : prop2cnf_partial_solve_wit_2.
Axiom proof_of_prop2cnf_partial_solve_wit_3_pure : prop2cnf_partial_solve_wit_3_pure.
Axiom proof_of_prop2cnf_partial_solve_wit_3 : prop2cnf_partial_solve_wit_3.
Axiom proof_of_prop2cnf_partial_solve_wit_4_pure : prop2cnf_partial_solve_wit_4_pure.
Axiom proof_of_prop2cnf_partial_solve_wit_4 : prop2cnf_partial_solve_wit_4.
Axiom proof_of_prop2cnf_partial_solve_wit_5_pure : prop2cnf_partial_solve_wit_5_pure.
Axiom proof_of_prop2cnf_partial_solve_wit_5 : prop2cnf_partial_solve_wit_5.
Axiom proof_of_prop2cnf_partial_solve_wit_6 : prop2cnf_partial_solve_wit_6.
Axiom proof_of_prop2cnf_partial_solve_wit_7_pure : prop2cnf_partial_solve_wit_7_pure.
Axiom proof_of_prop2cnf_partial_solve_wit_7 : prop2cnf_partial_solve_wit_7.
Axiom proof_of_prop2cnf_partial_solve_wit_8_pure : prop2cnf_partial_solve_wit_8_pure.
Axiom proof_of_prop2cnf_partial_solve_wit_8 : prop2cnf_partial_solve_wit_8.
Axiom proof_of_prop2cnf_partial_solve_wit_9_pure : prop2cnf_partial_solve_wit_9_pure.
Axiom proof_of_prop2cnf_partial_solve_wit_9 : prop2cnf_partial_solve_wit_9.
Axiom proof_of_prop2cnf_partial_solve_wit_10_pure : prop2cnf_partial_solve_wit_10_pure.
Axiom proof_of_prop2cnf_partial_solve_wit_10 : prop2cnf_partial_solve_wit_10.
Axiom proof_of_prop2cnf_partial_solve_wit_11_pure : prop2cnf_partial_solve_wit_11_pure.
Axiom proof_of_prop2cnf_partial_solve_wit_11 : prop2cnf_partial_solve_wit_11.
Axiom proof_of_prop2cnf_partial_solve_wit_12_pure : prop2cnf_partial_solve_wit_12_pure.
Axiom proof_of_prop2cnf_partial_solve_wit_12 : prop2cnf_partial_solve_wit_12.
Axiom proof_of_prop2cnf_partial_solve_wit_13_pure : prop2cnf_partial_solve_wit_13_pure.
Axiom proof_of_prop2cnf_partial_solve_wit_13 : prop2cnf_partial_solve_wit_13.
Axiom proof_of_prop2cnf_partial_solve_wit_14 : prop2cnf_partial_solve_wit_14.
Axiom proof_of_prop2cnf_partial_solve_wit_15_pure : prop2cnf_partial_solve_wit_15_pure.
Axiom proof_of_prop2cnf_partial_solve_wit_15 : prop2cnf_partial_solve_wit_15.
Axiom proof_of_prop2cnf_partial_solve_wit_16_pure : prop2cnf_partial_solve_wit_16_pure.
Axiom proof_of_prop2cnf_partial_solve_wit_16 : prop2cnf_partial_solve_wit_16.
Axiom proof_of_prop2cnf_partial_solve_wit_17_pure : prop2cnf_partial_solve_wit_17_pure.
Axiom proof_of_prop2cnf_partial_solve_wit_17 : prop2cnf_partial_solve_wit_17.
Axiom proof_of_prop2cnf_partial_solve_wit_18_pure : prop2cnf_partial_solve_wit_18_pure.
Axiom proof_of_prop2cnf_partial_solve_wit_18 : prop2cnf_partial_solve_wit_18.
Axiom proof_of_prop2cnf_partial_solve_wit_19_pure : prop2cnf_partial_solve_wit_19_pure.
Axiom proof_of_prop2cnf_partial_solve_wit_19 : prop2cnf_partial_solve_wit_19.
Axiom proof_of_prop2cnf_which_implies_wit_1 : prop2cnf_which_implies_wit_1.
Axiom proof_of_prop2cnf_which_implies_wit_2 : prop2cnf_which_implies_wit_2.
Axiom proof_of_prop2cnf_which_implies_wit_3 : prop2cnf_which_implies_wit_3.
Axiom proof_of_prop2cnf_which_implies_wit_4 : prop2cnf_which_implies_wit_4.
Axiom proof_of_prop2cnf_which_implies_wit_5 : prop2cnf_which_implies_wit_5.
Axiom proof_of_prop2cnf_which_implies_wit_6 : prop2cnf_which_implies_wit_6.
Axiom proof_of_prop2cnf_which_implies_wit_7 : prop2cnf_which_implies_wit_7.
Axiom proof_of_prop2cnf_which_implies_wit_8 : prop2cnf_which_implies_wit_8.
Axiom proof_of_prop2cnf_which_implies_wit_9 : prop2cnf_which_implies_wit_9.
Axiom proof_of_prop2cnf_which_implies_wit_10 : prop2cnf_which_implies_wit_10.
Axiom proof_of_prop2cnf_which_implies_wit_11 : prop2cnf_which_implies_wit_11.
Axiom proof_of_prop2cnf_which_implies_wit_12 : prop2cnf_which_implies_wit_12.
Axiom proof_of_prop2cnf_which_implies_wit_13 : prop2cnf_which_implies_wit_13.
Axiom proof_of_prop2cnf_which_implies_wit_14 : prop2cnf_which_implies_wit_14.

End VC_Correct.
