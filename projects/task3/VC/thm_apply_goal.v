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
From SimpleC.EE Require Import ast_lib.
From SimpleC.EE Require Import malloc.
From SimpleC.EE Require Import super_poly_sll2.
Local Open Scope sac.

(*----- Function sub_thm -----*)

Definition sub_thm_safety_wit_1 := 
forall (lis_pre: Z) (thm_pre: Z) (l: (@list var_sub)) (t: term) ,
  ((( &( "lis" ) )) # Ptr  |-> lis_pre)
  **  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
  **  (store_term thm_pre t )
  **  (sll_var_sub_list lis_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition sub_thm_safety_wit_2 := 
forall (lis_pre: Z) (thm_pre: Z) (t: term) (lis_next: Z) (l0: (@list var_sub)) (lis_cur: Z) (vs: var_sub) ,
  [| (thm_pre <> 0) |] 
  &&  [| (lis_pre <> 0) |]
  &&  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
  **  ((&((thm_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (t)))
  **  (store_term' thm_pre t )
  **  ((( &( "lis" ) )) # Ptr  |-> lis_pre)
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "cur")) # Ptr  |-> lis_cur)
  **  (store_var_sub lis_cur vs )
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "next")) # Ptr  |-> lis_next)
  **  (sll_var_sub_list lis_next l0 )
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition sub_thm_safety_wit_3 := 
forall (lis_pre: Z) (thm_pre: Z) (t: term) (lis_next: Z) (l0: (@list var_sub)) (lis_cur: Z) (vs: var_sub) ,
  [| ((termtypeID (t)) <> 3) |] 
  &&  [| (thm_pre <> 0) |] 
  &&  [| (lis_pre <> 0) |]
  &&  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
  **  ((&((thm_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (t)))
  **  (store_term' thm_pre t )
  **  ((( &( "lis" ) )) # Ptr  |-> lis_pre)
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "cur")) # Ptr  |-> lis_cur)
  **  (store_var_sub lis_cur vs )
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "next")) # Ptr  |-> lis_next)
  **  (sll_var_sub_list lis_next l0 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition sub_thm_return_wit_1 := 
forall (lis_pre: Z) (thm_pre: Z) (l: (@list var_sub)) (t: term) ,
  [| (lis_pre = 0) |]
  &&  (store_term thm_pre t )
  **  (sll_var_sub_list lis_pre l )
|--
  (sll_var_sub_list lis_pre l )
  **  (store_term_res thm_pre (thm_subst (t) (l)) )
.

Definition sub_thm_return_wit_2 := 
forall (lis_pre: Z) (thm_pre: Z) (l: (@list var_sub)) (t: term) (lis_next: Z) (l0: (@list var_sub)) (lis_cur: Z) (vs: var_sub) (sz: Z) (sy: Z) (z: Z) (y: Z) (sv: (@list Z)) (st: term) (qt: quant_type) (qvar: (@list Z)) (qterm: term) (retval: Z) ,
  [| (thm_pre <> 0) |] 
  &&  [| (t = (TermQuant (qt) (qvar) (qterm))) |] 
  &&  [| (vs = (VarSub (sv) (st))) |] 
  &&  [| ((termtypeID (t)) = 3) |] 
  &&  [| (thm_pre <> 0) |] 
  &&  [| (lis_pre <> 0) |]
  &&  (sll_var_sub_list lis_next l0 )
  **  (store_term_res retval (thm_subst ((term_subst_t (st) (sv) (qterm))) (l0)) )
  **  (store_term sz st )
  **  (store_string sy sv )
  **  ((&((thm_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (t)))
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z)
  **  (store_string y qvar )
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "cur")) # Ptr  |-> lis_cur)
  **  ((&((lis_cur)  # "var_sub" ->ₛ "var")) # Ptr  |-> sy)
  **  ((&((lis_cur)  # "var_sub" ->ₛ "sub_term")) # Ptr  |-> sz)
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "next")) # Ptr  |-> lis_next)
|--
  (sll_var_sub_list lis_pre l )
  **  (store_term_res retval (thm_subst (t) (l)) )
.

Definition sub_thm_return_wit_3 := 
forall (lis_pre: Z) (thm_pre: Z) (l: (@list var_sub)) (t: term) (lis_next: Z) (l0: (@list var_sub)) (lis_cur: Z) (vs: var_sub) ,
  [| ((termtypeID (t)) <> 3) |] 
  &&  [| (thm_pre <> 0) |] 
  &&  [| (lis_pre <> 0) |]
  &&  ((&((thm_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (t)))
  **  (store_term' thm_pre t )
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "cur")) # Ptr  |-> lis_cur)
  **  (store_var_sub lis_cur vs )
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "next")) # Ptr  |-> lis_next)
  **  (sll_var_sub_list lis_next l0 )
|--
  (sll_var_sub_list lis_pre l )
  **  (store_term_res 0 (thm_subst (t) (l)) )
.

Definition sub_thm_partial_solve_wit_1_pure := 
forall (lis_pre: Z) (thm_pre: Z) (l: (@list var_sub)) (t: term) ,
  [| (lis_pre <> 0) |]
  &&  ((( &( "lis" ) )) # Ptr  |-> lis_pre)
  **  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
  **  (store_term thm_pre t )
  **  (sll_var_sub_list lis_pre l )
|--
  [| (lis_pre <> 0) |]
.

Definition sub_thm_partial_solve_wit_1_aux := 
forall (lis_pre: Z) (thm_pre: Z) (l: (@list var_sub)) (t: term) ,
  [| (lis_pre <> 0) |]
  &&  (store_term thm_pre t )
  **  (sll_var_sub_list lis_pre l )
|--
  [| (lis_pre <> 0) |] 
  &&  [| (lis_pre <> 0) |]
  &&  (store_term thm_pre t )
  **  (sll_var_sub_list lis_pre l )
.

Definition sub_thm_partial_solve_wit_1 := sub_thm_partial_solve_wit_1_pure -> sub_thm_partial_solve_wit_1_aux.

Definition sub_thm_partial_solve_wit_2_pure := 
forall (lis_pre: Z) (thm_pre: Z) (t: term) (lis_next: Z) (l0: (@list var_sub)) (lis_cur: Z) (vs: var_sub) ,
  [| ((termtypeID (t)) = 3) |] 
  &&  [| (thm_pre <> 0) |] 
  &&  [| (lis_pre <> 0) |]
  &&  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
  **  ((&((thm_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (t)))
  **  (store_term' thm_pre t )
  **  ((( &( "lis" ) )) # Ptr  |-> lis_pre)
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "cur")) # Ptr  |-> lis_cur)
  **  (store_var_sub lis_cur vs )
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "next")) # Ptr  |-> lis_next)
  **  (sll_var_sub_list lis_next l0 )
|--
  [| ((termtypeID (t)) = 3) |] 
  &&  [| (thm_pre <> 0) |]
.

Definition sub_thm_partial_solve_wit_2_aux := 
forall (lis_pre: Z) (thm_pre: Z) (t: term) (lis_next: Z) (l0: (@list var_sub)) (lis_cur: Z) (vs: var_sub) ,
  [| ((termtypeID (t)) = 3) |] 
  &&  [| (thm_pre <> 0) |] 
  &&  [| (lis_pre <> 0) |]
  &&  ((&((thm_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (t)))
  **  (store_term' thm_pre t )
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "cur")) # Ptr  |-> lis_cur)
  **  (store_var_sub lis_cur vs )
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "next")) # Ptr  |-> lis_next)
  **  (sll_var_sub_list lis_next l0 )
|--
  [| ((termtypeID (t)) = 3) |] 
  &&  [| (thm_pre <> 0) |] 
  &&  [| ((termtypeID (t)) = 3) |] 
  &&  [| (thm_pre <> 0) |] 
  &&  [| (lis_pre <> 0) |]
  &&  ((&((thm_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (t)))
  **  (store_term' thm_pre t )
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "cur")) # Ptr  |-> lis_cur)
  **  (store_var_sub lis_cur vs )
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "next")) # Ptr  |-> lis_next)
  **  (sll_var_sub_list lis_next l0 )
.

Definition sub_thm_partial_solve_wit_2 := sub_thm_partial_solve_wit_2_pure -> sub_thm_partial_solve_wit_2_aux.

Definition sub_thm_partial_solve_wit_3_pure := 
forall (lis_pre: Z) (thm_pre: Z) (t: term) (lis_next: Z) (l0: (@list var_sub)) (lis_cur: Z) (vs: var_sub) (sz: Z) (sy: Z) (z: Z) (y: Z) (sv: (@list Z)) (st: term) (qt: quant_type) (qvar: (@list Z)) (qterm: term) ,
  [| (thm_pre <> 0) |] 
  &&  [| (t = (TermQuant (qt) (qvar) (qterm))) |] 
  &&  [| (vs = (VarSub (sv) (st))) |] 
  &&  [| ((termtypeID (t)) = 3) |] 
  &&  [| (thm_pre <> 0) |] 
  &&  [| (lis_pre <> 0) |]
  &&  ((( &( "den" ) )) # Ptr  |-> sz)
  **  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
  **  ((&((thm_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (t)))
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z)
  **  (store_string y qvar )
  **  (store_term z qterm )
  **  ((( &( "lis" ) )) # Ptr  |-> lis_pre)
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "cur")) # Ptr  |-> lis_cur)
  **  ((&((lis_cur)  # "var_sub" ->ₛ "var")) # Ptr  |-> sy)
  **  ((&((lis_cur)  # "var_sub" ->ₛ "sub_term")) # Ptr  |-> sz)
  **  (store_string sy sv )
  **  (store_term sz st )
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "next")) # Ptr  |-> lis_next)
  **  (sll_var_sub_list lis_next l0 )
|--
  [| (z <> 0) |] 
  &&  [| (sy <> 0) |] 
  &&  [| (sz <> 0) |]
.

Definition sub_thm_partial_solve_wit_3_aux := 
forall (lis_pre: Z) (thm_pre: Z) (t: term) (lis_next: Z) (l0: (@list var_sub)) (lis_cur: Z) (vs: var_sub) (sz: Z) (sy: Z) (z: Z) (y: Z) (sv: (@list Z)) (st: term) (qt: quant_type) (qvar: (@list Z)) (qterm: term) ,
  [| (thm_pre <> 0) |] 
  &&  [| (t = (TermQuant (qt) (qvar) (qterm))) |] 
  &&  [| (vs = (VarSub (sv) (st))) |] 
  &&  [| ((termtypeID (t)) = 3) |] 
  &&  [| (thm_pre <> 0) |] 
  &&  [| (lis_pre <> 0) |]
  &&  ((&((thm_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (t)))
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z)
  **  (store_string y qvar )
  **  (store_term z qterm )
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "cur")) # Ptr  |-> lis_cur)
  **  ((&((lis_cur)  # "var_sub" ->ₛ "var")) # Ptr  |-> sy)
  **  ((&((lis_cur)  # "var_sub" ->ₛ "sub_term")) # Ptr  |-> sz)
  **  (store_string sy sv )
  **  (store_term sz st )
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "next")) # Ptr  |-> lis_next)
  **  (sll_var_sub_list lis_next l0 )
|--
  [| (z <> 0) |] 
  &&  [| (sy <> 0) |] 
  &&  [| (sz <> 0) |] 
  &&  [| (thm_pre <> 0) |] 
  &&  [| (t = (TermQuant (qt) (qvar) (qterm))) |] 
  &&  [| (vs = (VarSub (sv) (st))) |] 
  &&  [| ((termtypeID (t)) = 3) |] 
  &&  [| (thm_pre <> 0) |] 
  &&  [| (lis_pre <> 0) |]
  &&  (store_term z qterm )
  **  (store_string sy sv )
  **  (store_term sz st )
  **  ((&((thm_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (t)))
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z)
  **  (store_string y qvar )
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "cur")) # Ptr  |-> lis_cur)
  **  ((&((lis_cur)  # "var_sub" ->ₛ "var")) # Ptr  |-> sy)
  **  ((&((lis_cur)  # "var_sub" ->ₛ "sub_term")) # Ptr  |-> sz)
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "next")) # Ptr  |-> lis_next)
  **  (sll_var_sub_list lis_next l0 )
.

Definition sub_thm_partial_solve_wit_3 := sub_thm_partial_solve_wit_3_pure -> sub_thm_partial_solve_wit_3_aux.

Definition sub_thm_partial_solve_wit_4 := 
forall (lis_pre: Z) (thm_pre: Z) (t: term) (lis_next: Z) (l0: (@list var_sub)) (lis_cur: Z) (vs: var_sub) (sz: Z) (sy: Z) (z: Z) (y: Z) (sv: (@list Z)) (st: term) (qt: quant_type) (qvar: (@list Z)) (qterm: term) (retval: Z) ,
  [| (thm_pre <> 0) |] 
  &&  [| (t = (TermQuant (qt) (qvar) (qterm))) |] 
  &&  [| (vs = (VarSub (sv) (st))) |] 
  &&  [| ((termtypeID (t)) = 3) |] 
  &&  [| (thm_pre <> 0) |] 
  &&  [| (lis_pre <> 0) |]
  &&  (store_term retval (term_subst_t (st) (sv) (qterm)) )
  **  (store_term sz st )
  **  (store_string sy sv )
  **  ((&((thm_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (t)))
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z)
  **  (store_string y qvar )
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "cur")) # Ptr  |-> lis_cur)
  **  ((&((lis_cur)  # "var_sub" ->ₛ "var")) # Ptr  |-> sy)
  **  ((&((lis_cur)  # "var_sub" ->ₛ "sub_term")) # Ptr  |-> sz)
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "next")) # Ptr  |-> lis_next)
  **  (sll_var_sub_list lis_next l0 )
|--
  [| (thm_pre <> 0) |] 
  &&  [| (t = (TermQuant (qt) (qvar) (qterm))) |] 
  &&  [| (vs = (VarSub (sv) (st))) |] 
  &&  [| ((termtypeID (t)) = 3) |] 
  &&  [| (thm_pre <> 0) |] 
  &&  [| (lis_pre <> 0) |]
  &&  (store_term retval (term_subst_t (st) (sv) (qterm)) )
  **  (sll_var_sub_list lis_next l0 )
  **  (store_term sz st )
  **  (store_string sy sv )
  **  ((&((thm_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (t)))
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z)
  **  (store_string y qvar )
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "cur")) # Ptr  |-> lis_cur)
  **  ((&((lis_cur)  # "var_sub" ->ₛ "var")) # Ptr  |-> sy)
  **  ((&((lis_cur)  # "var_sub" ->ₛ "sub_term")) # Ptr  |-> sz)
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "next")) # Ptr  |-> lis_next)
.

Definition sub_thm_which_implies_wit_1 := 
forall (l: (@list var_sub)) (t: term) (lis: Z) (thm: Z) ,
  [| (lis <> 0) |]
  &&  (store_term thm t )
  **  (sll_var_sub_list lis l )
|--
  EX (lis_next: Z)  (l0: (@list var_sub))  (lis_cur: Z)  (vs: var_sub) ,
  [| (thm <> 0) |]
  &&  ((&((thm)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (t)))
  **  (store_term' thm t )
  **  ((&((lis)  # "var_sub_list" ->ₛ "cur")) # Ptr  |-> lis_cur)
  **  (store_var_sub lis_cur vs )
  **  ((&((lis)  # "var_sub_list" ->ₛ "next")) # Ptr  |-> lis_next)
  **  (sll_var_sub_list lis_next l0 )
.

Definition sub_thm_which_implies_wit_2 := 
forall (t: term) (vs: var_sub) (thm: Z) (lis: Z) (lis_cur: Z) ,
  [| ((termtypeID (t)) = 3) |] 
  &&  [| (thm <> 0) |]
  &&  ((&((thm)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (t)))
  **  (store_term' thm t )
  **  ((&((lis)  # "var_sub_list" ->ₛ "cur")) # Ptr  |-> lis_cur)
  **  (store_var_sub lis_cur vs )
|--
  EX (sz: Z)  (sy: Z)  (z: Z)  (y: Z)  (sv: (@list Z))  (st: term)  (qt: quant_type)  (qvar: (@list Z))  (qterm: term) ,
  [| (thm <> 0) |] 
  &&  [| (t = (TermQuant (qt) (qvar) (qterm))) |] 
  &&  [| (vs = (VarSub (sv) (st))) |]
  &&  ((&((thm)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (t)))
  **  ((&((thm)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((thm)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((thm)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z)
  **  (store_string y qvar )
  **  (store_term z qterm )
  **  ((&((lis)  # "var_sub_list" ->ₛ "cur")) # Ptr  |-> lis_cur)
  **  ((&((lis_cur)  # "var_sub" ->ₛ "var")) # Ptr  |-> sy)
  **  ((&((lis_cur)  # "var_sub" ->ₛ "sub_term")) # Ptr  |-> sz)
  **  (store_string sy sv )
  **  (store_term sz st )
.

(*----- Function separate_imply -----*)

Definition separate_imply_safety_wit_1 := 
forall (t_pre: Z) (trm: term) ,
  [| (t_pre <> 0) |]
  &&  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition separate_imply_safety_wit_2 := 
forall (t_pre: Z) (trm: term) ,
  [| ((termtypeID (trm)) <> 2) |] 
  &&  [| (t_pre <> 0) |]
  &&  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition separate_imply_safety_wit_3 := 
forall (t_pre: Z) (trm: term) (v: Z) (v_2: Z) (lt: term) (rt: term) ,
  [| (v_2 <> 0) |] 
  &&  [| (trm = (TermApply (lt) (rt))) |] 
  &&  [| ((termtypeID (trm)) = 2) |] 
  &&  [| (t_pre <> 0) |]
  &&  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  (store_term' v_2 lt )
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition separate_imply_safety_wit_4 := 
forall (t_pre: Z) (trm: term) (v: Z) (v_2: Z) (lt: term) (rt: term) ,
  [| ((termtypeID (lt)) <> 2) |] 
  &&  [| (v_2 <> 0) |] 
  &&  [| (trm = (TermApply (lt) (rt))) |] 
  &&  [| ((termtypeID (trm)) = 2) |] 
  &&  [| (t_pre <> 0) |]
  &&  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  (store_term' v_2 lt )
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition separate_imply_safety_wit_5 := 
forall (t_pre: Z) (trm: term) (v: Z) (v_2: Z) (lt: term) (rt: term) (v_3: Z) (v_4: Z) (ll: term) (lr: term) ,
  [| (v_4 <> 0) |] 
  &&  [| (lt = (TermApply (ll) (lr))) |] 
  &&  [| ((termtypeID (lt)) = 2) |] 
  &&  [| (v_2 <> 0) |] 
  &&  [| (trm = (TermApply (lt) (rt))) |] 
  &&  [| ((termtypeID (trm)) = 2) |] 
  &&  [| (t_pre <> 0) |]
  &&  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_4)
  **  ((&((v_4)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (ll)))
  **  (store_term' v_4 ll )
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_term v_3 lr )
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition separate_imply_safety_wit_6 := 
forall (t_pre: Z) (trm: term) (v: Z) (v_2: Z) (lt: term) (rt: term) (v_3: Z) (v_4: Z) (ll: term) (lr: term) ,
  [| ((termtypeID (ll)) <> 1) |] 
  &&  [| (v_4 <> 0) |] 
  &&  [| (lt = (TermApply (ll) (lr))) |] 
  &&  [| ((termtypeID (lt)) = 2) |] 
  &&  [| (v_2 <> 0) |] 
  &&  [| (trm = (TermApply (lt) (rt))) |] 
  &&  [| ((termtypeID (trm)) = 2) |] 
  &&  [| (t_pre <> 0) |]
  &&  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_4)
  **  ((&((v_4)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (ll)))
  **  (store_term' v_4 ll )
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_term v_3 lr )
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition separate_imply_safety_wit_7 := 
forall (t_pre: Z) (trm: term) (v: Z) (v_2: Z) (lt: term) (rt: term) (v_3: Z) (v_4: Z) (ll: term) (lr: term) (llctype: const_type) (llcctnt: Z) ,
  [| (ll = (TermConst (llctype) (llcctnt))) |] 
  &&  [| ((termtypeID (ll)) = 1) |] 
  &&  [| (v_4 <> 0) |] 
  &&  [| (lt = (TermApply (ll) (lr))) |] 
  &&  [| ((termtypeID (lt)) = 2) |] 
  &&  [| (v_2 <> 0) |] 
  &&  [| (trm = (TermApply (lt) (rt))) |] 
  &&  [| ((termtypeID (trm)) = 2) |] 
  &&  [| (t_pre <> 0) |]
  &&  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_4)
  **  ((&((v_4)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (llctype)))
  **  ((&((v_4)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> llcctnt)
  **  ((&((v_4)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (ll)))
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_term v_3 lr )
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  [| (7 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 7) |]
.

Definition separate_imply_safety_wit_8 := 
forall (t_pre: Z) (trm: term) (v: Z) (v_2: Z) (lt: term) (rt: term) (v_3: Z) (v_4: Z) (ll: term) (lr: term) (llctype: const_type) (llcctnt: Z) ,
  [| ((ctID (llctype)) <> 7) |] 
  &&  [| (ll = (TermConst (llctype) (llcctnt))) |] 
  &&  [| ((termtypeID (ll)) = 1) |] 
  &&  [| (v_4 <> 0) |] 
  &&  [| (lt = (TermApply (ll) (lr))) |] 
  &&  [| ((termtypeID (lt)) = 2) |] 
  &&  [| (v_2 <> 0) |] 
  &&  [| (trm = (TermApply (lt) (rt))) |] 
  &&  [| ((termtypeID (trm)) = 2) |] 
  &&  [| (t_pre <> 0) |]
  &&  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_4)
  **  ((&((v_4)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (llctype)))
  **  ((&((v_4)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> llcctnt)
  **  ((&((v_4)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (ll)))
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_term v_3 lr )
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition separate_imply_return_wit_1 := 
forall (t_pre: Z) (trm: term) ,
  [| ((termtypeID (trm)) <> 2) |] 
  &&  [| (t_pre <> 0) |]
  &&  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
|--
  (store_imply_res 0 (sep_impl (trm)) )
.

Definition separate_imply_return_wit_2 := 
forall (t_pre: Z) (trm: term) (v: Z) (v_2: Z) (lt: term) (rt: term) ,
  [| ((termtypeID (lt)) <> 2) |] 
  &&  [| (v_2 <> 0) |] 
  &&  [| (trm = (TermApply (lt) (rt))) |] 
  &&  [| ((termtypeID (trm)) = 2) |] 
  &&  [| (t_pre <> 0) |]
  &&  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  (store_term' v_2 lt )
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  (store_imply_res 0 (sep_impl (trm)) )
.

Definition separate_imply_return_wit_3 := 
forall (t_pre: Z) (trm: term) (v: Z) (v_2: Z) (lt: term) (rt: term) (v_3: Z) (v_4: Z) (ll: term) (lr: term) ,
  [| ((termtypeID (ll)) <> 1) |] 
  &&  [| (v_4 <> 0) |] 
  &&  [| (lt = (TermApply (ll) (lr))) |] 
  &&  [| ((termtypeID (lt)) = 2) |] 
  &&  [| (v_2 <> 0) |] 
  &&  [| (trm = (TermApply (lt) (rt))) |] 
  &&  [| ((termtypeID (trm)) = 2) |] 
  &&  [| (t_pre <> 0) |]
  &&  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_4)
  **  ((&((v_4)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (ll)))
  **  (store_term' v_4 ll )
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_term v_3 lr )
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  (store_imply_res 0 (sep_impl (trm)) )
.

Definition separate_imply_return_wit_4 := 
forall (t_pre: Z) (trm: term) (v: Z) (v_2: Z) (lt: term) (rt: term) (v_3: Z) (v_4: Z) (ll: term) (lr: term) (llctype: const_type) (llcctnt: Z) ,
  [| ((ctID (llctype)) <> 7) |] 
  &&  [| (ll = (TermConst (llctype) (llcctnt))) |] 
  &&  [| ((termtypeID (ll)) = 1) |] 
  &&  [| (v_4 <> 0) |] 
  &&  [| (lt = (TermApply (ll) (lr))) |] 
  &&  [| ((termtypeID (lt)) = 2) |] 
  &&  [| (v_2 <> 0) |] 
  &&  [| (trm = (TermApply (lt) (rt))) |] 
  &&  [| ((termtypeID (trm)) = 2) |] 
  &&  [| (t_pre <> 0) |]
  &&  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_4)
  **  ((&((v_4)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (llctype)))
  **  ((&((v_4)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> llcctnt)
  **  ((&((v_4)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (ll)))
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_term v_3 lr )
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  (store_imply_res 0 (sep_impl (trm)) )
.

Definition separate_imply_return_wit_5 := 
forall (t_pre: Z) (trm: term) (v: Z) (v_2: Z) (lt: term) (rt: term) (v_3: Z) (v_4: Z) (ll: term) (lr: term) (llctype: const_type) (llcctnt: Z) (retval: Z) ,
  [| ((ctID (llctype)) = 7) |] 
  &&  [| (ll = (TermConst (llctype) (llcctnt))) |] 
  &&  [| ((termtypeID (ll)) = 1) |] 
  &&  [| (v_4 <> 0) |] 
  &&  [| (lt = (TermApply (ll) (lr))) |] 
  &&  [| ((termtypeID (lt)) = 2) |] 
  &&  [| (v_2 <> 0) |] 
  &&  [| (trm = (TermApply (lt) (rt))) |] 
  &&  [| ((termtypeID (trm)) = 2) |] 
  &&  [| (t_pre <> 0) |]
  &&  (store_ImplyProp retval v_3 v lr rt )
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_4)
  **  ((&((v_4)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (llctype)))
  **  ((&((v_4)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> llcctnt)
  **  ((&((v_4)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (ll)))
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_3)
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  (store_imply_res retval (sep_impl (trm)) )
.

Definition separate_imply_partial_solve_wit_1 := 
forall (t_pre: Z) (trm: term) ,
  (store_term t_pre trm )
|--
  (store_term t_pre trm )
.

Definition separate_imply_partial_solve_wit_2_pure := 
forall (t_pre: Z) (trm: term) ,
  [| ((termtypeID (trm)) = 2) |] 
  &&  [| (t_pre <> 0) |]
  &&  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
|--
  [| (t_pre <> 0) |] 
  &&  [| ((termtypeID (trm)) = 2) |]
.

Definition separate_imply_partial_solve_wit_2_aux := 
forall (t_pre: Z) (trm: term) ,
  [| ((termtypeID (trm)) = 2) |] 
  &&  [| (t_pre <> 0) |]
  &&  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
|--
  [| (t_pre <> 0) |] 
  &&  [| ((termtypeID (trm)) = 2) |] 
  &&  [| ((termtypeID (trm)) = 2) |] 
  &&  [| (t_pre <> 0) |]
  &&  (store_term' t_pre trm )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
.

Definition separate_imply_partial_solve_wit_2 := separate_imply_partial_solve_wit_2_pure -> separate_imply_partial_solve_wit_2_aux.

Definition separate_imply_partial_solve_wit_3 := 
forall (t_pre: Z) (trm: term) (v: Z) (v_2: Z) (lt: term) (rt: term) ,
  [| (trm = (TermApply (lt) (rt))) |] 
  &&  [| ((termtypeID (trm)) = 2) |] 
  &&  [| (t_pre <> 0) |]
  &&  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  (store_term v_2 lt )
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  [| (trm = (TermApply (lt) (rt))) |] 
  &&  [| ((termtypeID (trm)) = 2) |] 
  &&  [| (t_pre <> 0) |]
  &&  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  (store_term v_2 lt )
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
.

Definition separate_imply_partial_solve_wit_4_pure := 
forall (t_pre: Z) (trm: term) (v_2: Z) (v: Z) (lt: term) (rt: term) ,
  [| ((termtypeID (lt)) = 2) |] 
  &&  [| (v <> 0) |] 
  &&  [| (trm = (TermApply (lt) (rt))) |] 
  &&  [| ((termtypeID (trm)) = 2) |] 
  &&  [| (t_pre <> 0) |]
  &&  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v)
  **  ((&((v)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  (store_term' v lt )
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_2)
  **  (store_term v_2 rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  [| (v <> 0) |] 
  &&  [| ((termtypeID (lt)) = 2) |]
.

Definition separate_imply_partial_solve_wit_4_aux := 
forall (t_pre: Z) (trm: term) (v: Z) (v_2: Z) (lt: term) (rt: term) ,
  [| ((termtypeID (lt)) = 2) |] 
  &&  [| (v_2 <> 0) |] 
  &&  [| (trm = (TermApply (lt) (rt))) |] 
  &&  [| ((termtypeID (trm)) = 2) |] 
  &&  [| (t_pre <> 0) |]
  &&  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  (store_term' v_2 lt )
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  [| (v_2 <> 0) |] 
  &&  [| ((termtypeID (lt)) = 2) |] 
  &&  [| ((termtypeID (lt)) = 2) |] 
  &&  [| (v_2 <> 0) |] 
  &&  [| (trm = (TermApply (lt) (rt))) |] 
  &&  [| ((termtypeID (trm)) = 2) |] 
  &&  [| (t_pre <> 0) |]
  &&  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  (store_term' v_2 lt )
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
.

Definition separate_imply_partial_solve_wit_4 := separate_imply_partial_solve_wit_4_pure -> separate_imply_partial_solve_wit_4_aux.

Definition separate_imply_partial_solve_wit_5 := 
forall (t_pre: Z) (trm: term) (v: Z) (v_2: Z) (lt: term) (rt: term) (v_3: Z) (v_4: Z) (ll: term) (lr: term) ,
  [| (lt = (TermApply (ll) (lr))) |] 
  &&  [| ((termtypeID (lt)) = 2) |] 
  &&  [| (v_2 <> 0) |] 
  &&  [| (trm = (TermApply (lt) (rt))) |] 
  &&  [| ((termtypeID (trm)) = 2) |] 
  &&  [| (t_pre <> 0) |]
  &&  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_4)
  **  (store_term v_4 ll )
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_term v_3 lr )
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  [| (lt = (TermApply (ll) (lr))) |] 
  &&  [| ((termtypeID (lt)) = 2) |] 
  &&  [| (v_2 <> 0) |] 
  &&  [| (trm = (TermApply (lt) (rt))) |] 
  &&  [| ((termtypeID (trm)) = 2) |] 
  &&  [| (t_pre <> 0) |]
  &&  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_4)
  **  (store_term v_4 ll )
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_term v_3 lr )
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
.

Definition separate_imply_partial_solve_wit_6_pure := 
forall (t_pre: Z) (trm: term) (v_2: Z) (v_3: Z) (lt: term) (rt: term) (v_4: Z) (v: Z) (ll: term) (lr: term) ,
  [| ((termtypeID (ll)) = 1) |] 
  &&  [| (v <> 0) |] 
  &&  [| (lt = (TermApply (ll) (lr))) |] 
  &&  [| ((termtypeID (lt)) = 2) |] 
  &&  [| (v_3 <> 0) |] 
  &&  [| (trm = (TermApply (lt) (rt))) |] 
  &&  [| ((termtypeID (trm)) = 2) |] 
  &&  [| (t_pre <> 0) |]
  &&  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_3)
  **  ((&((v_3)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v)
  **  ((&((v)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (ll)))
  **  (store_term' v ll )
  **  ((&((v_3)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_4)
  **  (store_term v_4 lr )
  **  ((&((v_3)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_2)
  **  (store_term v_2 rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  [| (v <> 0) |] 
  &&  [| ((termtypeID (ll)) = 1) |]
.

Definition separate_imply_partial_solve_wit_6_aux := 
forall (t_pre: Z) (trm: term) (v: Z) (v_2: Z) (lt: term) (rt: term) (v_3: Z) (v_4: Z) (ll: term) (lr: term) ,
  [| ((termtypeID (ll)) = 1) |] 
  &&  [| (v_4 <> 0) |] 
  &&  [| (lt = (TermApply (ll) (lr))) |] 
  &&  [| ((termtypeID (lt)) = 2) |] 
  &&  [| (v_2 <> 0) |] 
  &&  [| (trm = (TermApply (lt) (rt))) |] 
  &&  [| ((termtypeID (trm)) = 2) |] 
  &&  [| (t_pre <> 0) |]
  &&  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_4)
  **  ((&((v_4)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (ll)))
  **  (store_term' v_4 ll )
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_term v_3 lr )
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  [| (v_4 <> 0) |] 
  &&  [| ((termtypeID (ll)) = 1) |] 
  &&  [| ((termtypeID (ll)) = 1) |] 
  &&  [| (v_4 <> 0) |] 
  &&  [| (lt = (TermApply (ll) (lr))) |] 
  &&  [| ((termtypeID (lt)) = 2) |] 
  &&  [| (v_2 <> 0) |] 
  &&  [| (trm = (TermApply (lt) (rt))) |] 
  &&  [| ((termtypeID (trm)) = 2) |] 
  &&  [| (t_pre <> 0) |]
  &&  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_4)
  **  (store_term' v_4 ll )
  **  ((&((v_4)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (ll)))
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_term v_3 lr )
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
.

Definition separate_imply_partial_solve_wit_6 := separate_imply_partial_solve_wit_6_pure -> separate_imply_partial_solve_wit_6_aux.

Definition separate_imply_partial_solve_wit_7 := 
forall (t_pre: Z) (trm: term) (v: Z) (v_2: Z) (lt: term) (rt: term) (v_3: Z) (v_4: Z) (ll: term) (lr: term) (llctype: const_type) (llcctnt: Z) ,
  [| ((ctID (llctype)) = 7) |] 
  &&  [| (ll = (TermConst (llctype) (llcctnt))) |] 
  &&  [| ((termtypeID (ll)) = 1) |] 
  &&  [| (v_4 <> 0) |] 
  &&  [| (lt = (TermApply (ll) (lr))) |] 
  &&  [| ((termtypeID (lt)) = 2) |] 
  &&  [| (v_2 <> 0) |] 
  &&  [| (trm = (TermApply (lt) (rt))) |] 
  &&  [| ((termtypeID (trm)) = 2) |] 
  &&  [| (t_pre <> 0) |]
  &&  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_4)
  **  ((&((v_4)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (llctype)))
  **  ((&((v_4)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> llcctnt)
  **  ((&((v_4)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (ll)))
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_term v_3 lr )
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  [| ((ctID (llctype)) = 7) |] 
  &&  [| (ll = (TermConst (llctype) (llcctnt))) |] 
  &&  [| ((termtypeID (ll)) = 1) |] 
  &&  [| (v_4 <> 0) |] 
  &&  [| (lt = (TermApply (ll) (lr))) |] 
  &&  [| ((termtypeID (lt)) = 2) |] 
  &&  [| (v_2 <> 0) |] 
  &&  [| (trm = (TermApply (lt) (rt))) |] 
  &&  [| ((termtypeID (trm)) = 2) |] 
  &&  [| (t_pre <> 0) |]
  &&  (store_term v_3 lr )
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_4)
  **  ((&((v_4)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (llctype)))
  **  ((&((v_4)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> llcctnt)
  **  ((&((v_4)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (ll)))
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_3)
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
.

Definition separate_imply_which_implies_wit_1 := 
forall (trm: term) (t: Z) ,
  (store_term t trm )
|--
  [| (t <> 0) |]
  &&  ((&((t)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t trm )
.

Definition separate_imply_which_implies_wit_2 := 
forall (trm: term) (t: Z) ,
  [| (t <> 0) |] 
  &&  [| ((termtypeID (trm)) = 2) |]
  &&  (store_term' t trm )
|--
  EX (v: Z)  (v_2: Z)  (lt: term)  (rt: term) ,
  [| (trm = (TermApply (lt) (rt))) |]
  &&  ((&((t)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  (store_term v_2 lt )
  **  ((&((t)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v rt )
.

Definition separate_imply_which_implies_wit_3 := 
forall (lt: term) (t: Z) (v: Z) ,
  ((&((t)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v)
  **  (store_term v lt )
|--
  [| (v <> 0) |]
  &&  ((&((t)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v)
  **  ((&((v)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  (store_term' v lt )
.

Definition separate_imply_which_implies_wit_4 := 
forall (lt: term) (t: Z) (v_3: Z) ,
  [| (v_3 <> 0) |] 
  &&  [| ((termtypeID (lt)) = 2) |]
  &&  ((&((t)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_3)
  **  (store_term' v_3 lt )
|--
  EX (v: Z)  (v_2: Z)  (ll: term)  (lr: term) ,
  [| (lt = (TermApply (ll) (lr))) |]
  &&  ((&((t)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_3)
  **  ((&((v_3)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  (store_term v_2 ll )
  **  ((&((v_3)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v lr )
.

Definition separate_imply_which_implies_wit_5 := 
forall (ll: term) (t: Z) (v: Z) (v_2: Z) ,
  ((&((t)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v)
  **  ((&((v)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  (store_term v_2 ll )
|--
  [| (v_2 <> 0) |]
  &&  ((&((t)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v)
  **  ((&((v)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (ll)))
  **  (store_term' v_2 ll )
.

Definition separate_imply_which_implies_wit_6 := 
forall (ll: term) (t: Z) (v: Z) (v_2: Z) ,
  [| (v_2 <> 0) |] 
  &&  [| ((termtypeID (ll)) = 1) |]
  &&  ((&((t)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v)
  **  ((&((v)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  (store_term' v_2 ll )
|--
  EX (llctype: const_type)  (llcctnt: Z) ,
  [| (ll = (TermConst (llctype) (llcctnt))) |]
  &&  ((&((t)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v)
  **  ((&((v)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (llctype)))
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> llcctnt)
.

(*----- Function check_list_gen -----*)

Definition check_list_gen_safety_wit_1 := 
forall (target_pre: Z) (thm_pre: Z) (targ: term) (theo: term) ,
  ((( &( "target" ) )) # Ptr  |-> target_pre)
  **  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
  **  (store_term thm_pre theo )
  **  (store_term target_pre targ )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition check_list_gen_safety_wit_2 := 
forall (target_pre: Z) (thm_pre: Z) (targ: term) (theo: term) ,
  [| (thm_pre <> 0) |]
  &&  ((( &( "target" ) )) # Ptr  |-> target_pre)
  **  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
  **  (store_term thm_pre theo )
  **  (store_term target_pre targ )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition check_list_gen_safety_wit_3 := 
forall (target_pre: Z) (thm_pre: Z) (targ: term) (theo: term) ,
  [| (thm_pre = 0) |]
  &&  ((( &( "target" ) )) # Ptr  |-> target_pre)
  **  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
  **  (store_term thm_pre theo )
  **  (store_term target_pre targ )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition check_list_gen_safety_wit_4 := 
forall (target_pre: Z) (thm_pre: Z) (targ: term) (theo: term) ,
  [| (target_pre = 0) |] 
  &&  [| (thm_pre <> 0) |]
  &&  ((( &( "target" ) )) # Ptr  |-> target_pre)
  **  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
  **  (store_term thm_pre theo )
  **  (store_term target_pre targ )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition check_list_gen_safety_wit_5 := 
forall (target_pre: Z) (thm_pre: Z) (targ: term) (theo: term) ,
  [| (target_pre <> 0) |] 
  &&  [| (thm_pre <> 0) |]
  &&  ((( &( "check_list" ) )) # Ptr  |->_)
  **  ((( &( "target" ) )) # Ptr  |-> target_pre)
  **  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
  **  (store_term thm_pre theo )
  **  (store_term target_pre targ )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition check_list_gen_safety_wit_6 := 
forall (target_pre: Z) (thm_pre: Z) (targ: term) (theo: term) (check_list: Z) (l: (@list term)) ,
  [| (target_pre <> 0) |] 
  &&  [| (thm_pre <> 0) |]
  &&  ((( &( "target" ) )) # Ptr  |-> target_pre)
  **  (store_term thm_pre theo )
  **  (store_term target_pre targ )
  **  ((( &( "check_list" ) )) # Ptr  |-> check_list)
  **  (sll_term_list check_list l )
  **  ((( &( "tail_ptr" ) )) # Ptr  |-> ( &( "check_list" ) ))
  **  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition check_list_gen_safety_wit_7 := 
forall (target_pre: Z) (thm_pre: Z) (targ: term) (theo: term) (check_list: Z) (l: (@list term)) ,
  [| (thm_pre = 0) |] 
  &&  [| (target_pre <> 0) |] 
  &&  [| (thm_pre <> 0) |]
  &&  ((( &( "target" ) )) # Ptr  |-> target_pre)
  **  (store_term thm_pre theo )
  **  (store_term target_pre targ )
  **  ((( &( "check_list" ) )) # Ptr  |-> check_list)
  **  (sll_term_list check_list l )
  **  ((( &( "tail_ptr" ) )) # Ptr  |-> ( &( "check_list" ) ))
  **  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
|--
  [| False |]
.

Definition check_list_gen_safety_wit_8 := 
forall (target_pre: Z) (thm_pre: Z) (targ: term) (theo: term) (check_list: Z) (l: (@list term)) (retval_2: Z) (retval: Z) ,
  [| (retval_2 = 0) |] 
  &&  [| (retval_2 = (term_alpha_eqn (theo) (targ))) |] 
  &&  [| (thm_pre <> 0) |] 
  &&  [| (target_pre <> 0) |] 
  &&  [| (thm_pre <> 0) |]
  &&  (store_imply_res retval (sep_impl (theo)) )
  **  ((( &( "p" ) )) # Ptr  |-> retval)
  **  (store_term target_pre targ )
  **  ((( &( "target" ) )) # Ptr  |-> target_pre)
  **  ((( &( "check_list" ) )) # Ptr  |-> check_list)
  **  (sll_term_list check_list l )
  **  ((( &( "tail_ptr" ) )) # Ptr  |-> ( &( "check_list" ) ))
  **  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition check_list_gen_safety_wit_9 := 
forall (target_pre: Z) (thm_pre: Z) (targ: term) (theo: term) (check_list: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval = (term_alpha_eqn (theo) (targ))) |] 
  &&  [| (thm_pre <> 0) |] 
  &&  [| (target_pre <> 0) |] 
  &&  [| (thm_pre <> 0) |]
  &&  (store_imply_res retval_2 (sep_impl (theo)) )
  **  ((( &( "p" ) )) # Ptr  |-> retval_2)
  **  (store_term target_pre targ )
  **  ((( &( "target" ) )) # Ptr  |-> target_pre)
  **  ((( &( "check_list" ) )) # Ptr  |-> check_list)
  **  ((( &( "tail_ptr" ) )) # Ptr  |-> ( &( "check_list" ) ))
  **  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition check_list_gen_safety_wit_10 := 
forall (target_pre: Z) (thm_pre: Z) (targ: term) (theo: term) (check_list: Z) (l: (@list term)) (retval: Z) (retval_2: Z) (retval_3: Z) (p_concl: Z) (p_assum: Z) (p_assum_2: term) (p_concl_2: term) ,
  [| ((sep_impl (theo)) = (imply_res_Cont (p_assum_2) (p_concl_2))) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval = (term_alpha_eqn (theo) (targ))) |] 
  &&  [| (thm_pre <> 0) |] 
  &&  [| (target_pre <> 0) |] 
  &&  [| (thm_pre <> 0) |]
  &&  ((( &( "p" ) )) # Ptr  |-> retval_2)
  **  ((&((retval_2)  # "imply_prop" ->ₛ "assum")) # Ptr  |-> p_assum)
  **  (store_term p_assum p_assum_2 )
  **  ((&((retval_2)  # "imply_prop" ->ₛ "concl")) # Ptr  |-> p_concl)
  **  (store_term p_concl p_concl_2 )
  **  ((&((retval_3)  # "term_list" ->ₛ "element")) # Ptr  |-> p_assum)
  **  ((&((retval_3)  # "term_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "new_node" ) )) # Ptr  |-> retval_3)
  **  (store_term target_pre targ )
  **  ((( &( "target" ) )) # Ptr  |-> target_pre)
  **  ((( &( "check_list" ) )) # Ptr  |-> check_list)
  **  (sll_term_list check_list l )
  **  ((( &( "tail_ptr" ) )) # Ptr  |-> ( &( "check_list" ) ))
  **  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition check_list_gen_entail_wit_1 := 
forall (target_pre: Z) (thm_pre: Z) (targ: term) (theo: term) ,
  [| (target_pre <> 0) |] 
  &&  [| (thm_pre <> 0) |]
  &&  (sll_term_list 0 nil )
  **  (store_term thm_pre theo )
  **  (store_term target_pre targ )
|--
  EX (l: (@list term)) ,
  [| (target_pre <> 0) |] 
  &&  [| (thm_pre <> 0) |]
  &&  (store_term thm_pre theo )
  **  (store_term target_pre targ )
  **  (sll_term_list 0 l )
.

Definition check_list_gen_entail_wit_2 := 
forall (target_pre: Z) (thm_pre: Z) (targ: term) (theo: term) (check_list: Z) (l_2: (@list term)) (retval_2: Z) (retval_3: Z) (retval: Z) (p_concl: Z) (p_assum: Z) (p_assum_2: term) (p_concl_2: term) (y: Z) (z: Z) ,
  [| ((sep_impl (theo)) = (imply_res_Cont (p_assum_2) (p_concl_2))) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| (retval_2 = (term_alpha_eqn (theo) (targ))) |] 
  &&  [| (thm_pre <> 0) |] 
  &&  [| (target_pre <> 0) |] 
  &&  [| (thm_pre <> 0) |]
  &&  (store_term y p_assum_2 )
  **  (store_term z p_concl_2 )
  **  ((&((retval)  # "term_list" ->ₛ "element")) # Ptr  |-> p_assum)
  **  ((&((retval)  # "term_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_term target_pre targ )
  **  (sll_term_list check_list l_2 )
  **  ((( &( "tail_ptr" ) )) # Ptr  |-> &((retval)  # "term_list" ->ₛ "next"))
  **  ((( &( "thm" ) )) # Ptr  |-> p_concl)
|--
  EX (l: (@list term)) ,
  [| (target_pre <> 0) |] 
  &&  [| (thm_pre <> 0) |]
  &&  (store_term thm_pre theo )
  **  (store_term target_pre targ )
  **  (sll_term_list retval l )
  **  ((( &( "tail_ptr" ) )) # Ptr  |-> ( &( "check_list" ) ))
  **  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
.

Definition check_list_gen_return_wit_1 := 
forall (target_pre: Z) (thm_pre: Z) (targ: term) (theo: term) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval = (term_alpha_eqn (theo) (targ))) |] 
  &&  [| (thm_pre <> 0) |] 
  &&  [| (target_pre <> 0) |] 
  &&  [| (thm_pre <> 0) |]
  &&  (store_imply_res retval_2 (sep_impl (theo)) )
  **  (store_term target_pre targ )
|--
  (store_term thm_pre theo )
  **  (store_term target_pre targ )
  **  (sll_term_list 0 (gen_pre (theo) (targ)) )
.

Definition check_list_gen_return_wit_2_1 := 
forall (target_pre: Z) (thm_pre: Z) (targ: term) (theo: term) ,
  [| (target_pre = 0) |] 
  &&  [| (thm_pre <> 0) |]
  &&  (store_term thm_pre theo )
  **  (store_term target_pre targ )
|--
  (store_term thm_pre theo )
  **  (store_term target_pre targ )
  **  (sll_term_list 0 (gen_pre (theo) (targ)) )
.

Definition check_list_gen_return_wit_2_2 := 
forall (target_pre: Z) (thm_pre: Z) (targ: term) (theo: term) ,
  [| (thm_pre = 0) |]
  &&  (store_term thm_pre theo )
  **  (store_term target_pre targ )
|--
  (store_term thm_pre theo )
  **  (store_term target_pre targ )
  **  (sll_term_list 0 (gen_pre (theo) (targ)) )
.

Definition check_list_gen_return_wit_3 := 
forall (target_pre: Z) (thm_pre: Z) (targ: term) (theo: term) (check_list: Z) (l: (@list term)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = (term_alpha_eqn (theo) (targ))) |] 
  &&  [| (thm_pre <> 0) |] 
  &&  [| (target_pre <> 0) |] 
  &&  [| (thm_pre <> 0) |]
  &&  (store_term thm_pre theo )
  **  (store_term target_pre targ )
  **  (sll_term_list check_list l )
|--
  (store_term thm_pre theo )
  **  (store_term target_pre targ )
  **  (sll_term_list check_list (gen_pre (theo) (targ)) )
.

Definition check_list_gen_partial_solve_wit_1_pure := 
forall (target_pre: Z) (thm_pre: Z) (targ: term) (theo: term) ,
  [| (target_pre <> 0) |] 
  &&  [| (thm_pre <> 0) |]
  &&  ((( &( "tail_ptr" ) )) # Ptr  |-> ( &( "check_list" ) ))
  **  ((( &( "check_list" ) )) # Ptr  |-> 0)
  **  ((( &( "target" ) )) # Ptr  |-> target_pre)
  **  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
  **  (store_term thm_pre theo )
  **  (store_term target_pre targ )
|--
  [| (0 = 0) |]
.

Definition check_list_gen_partial_solve_wit_1_aux := 
forall (target_pre: Z) (thm_pre: Z) (targ: term) (theo: term) ,
  [| (target_pre <> 0) |] 
  &&  [| (thm_pre <> 0) |]
  &&  (store_term thm_pre theo )
  **  (store_term target_pre targ )
|--
  [| (0 = 0) |] 
  &&  [| (target_pre <> 0) |] 
  &&  [| (thm_pre <> 0) |]
  &&  (store_term thm_pre theo )
  **  (store_term target_pre targ )
.

Definition check_list_gen_partial_solve_wit_1 := check_list_gen_partial_solve_wit_1_pure -> check_list_gen_partial_solve_wit_1_aux.

Definition check_list_gen_partial_solve_wit_2 := 
forall (target_pre: Z) (thm_pre: Z) (targ: term) (theo: term) (check_list: Z) (l: (@list term)) ,
  [| (thm_pre <> 0) |] 
  &&  [| (target_pre <> 0) |] 
  &&  [| (thm_pre <> 0) |]
  &&  (store_term thm_pre theo )
  **  (store_term target_pre targ )
  **  (sll_term_list check_list l )
|--
  [| (thm_pre <> 0) |] 
  &&  [| (target_pre <> 0) |] 
  &&  [| (thm_pre <> 0) |]
  &&  (store_term thm_pre theo )
  **  (store_term target_pre targ )
  **  (sll_term_list check_list l )
.

Definition check_list_gen_partial_solve_wit_3 := 
forall (target_pre: Z) (thm_pre: Z) (targ: term) (theo: term) (check_list: Z) (l: (@list term)) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = (term_alpha_eqn (theo) (targ))) |] 
  &&  [| (thm_pre <> 0) |] 
  &&  [| (target_pre <> 0) |] 
  &&  [| (thm_pre <> 0) |]
  &&  (store_term thm_pre theo )
  **  (store_term target_pre targ )
  **  (sll_term_list check_list l )
|--
  [| (retval = 0) |] 
  &&  [| (retval = (term_alpha_eqn (theo) (targ))) |] 
  &&  [| (thm_pre <> 0) |] 
  &&  [| (target_pre <> 0) |] 
  &&  [| (thm_pre <> 0) |]
  &&  (store_term thm_pre theo )
  **  (store_term target_pre targ )
  **  (sll_term_list check_list l )
.

Definition check_list_gen_partial_solve_wit_4 := 
forall (target_pre: Z) (thm_pre: Z) (targ: term) (theo: term) (check_list: Z) (l: (@list term)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval = (term_alpha_eqn (theo) (targ))) |] 
  &&  [| (thm_pre <> 0) |] 
  &&  [| (target_pre <> 0) |] 
  &&  [| (thm_pre <> 0) |]
  &&  (store_imply_res retval_2 (sep_impl (theo)) )
  **  (store_term target_pre targ )
  **  (sll_term_list check_list l )
|--
  [| (retval_2 = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval = (term_alpha_eqn (theo) (targ))) |] 
  &&  [| (thm_pre <> 0) |] 
  &&  [| (target_pre <> 0) |] 
  &&  [| (thm_pre <> 0) |]
  &&  (sll_term_list check_list l )
  **  (store_imply_res retval_2 (sep_impl (theo)) )
  **  (store_term target_pre targ )
.

Definition check_list_gen_partial_solve_wit_5 := 
forall (target_pre: Z) (thm_pre: Z) (targ: term) (theo: term) (check_list: Z) (l: (@list term)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval = (term_alpha_eqn (theo) (targ))) |] 
  &&  [| (thm_pre <> 0) |] 
  &&  [| (target_pre <> 0) |] 
  &&  [| (thm_pre <> 0) |]
  &&  (store_imply_res retval_2 (sep_impl (theo)) )
  **  (store_term target_pre targ )
  **  (sll_term_list check_list l )
|--
  [| (retval_2 <> 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval = (term_alpha_eqn (theo) (targ))) |] 
  &&  [| (thm_pre <> 0) |] 
  &&  [| (target_pre <> 0) |] 
  &&  [| (thm_pre <> 0) |]
  &&  (store_imply_res retval_2 (sep_impl (theo)) )
  **  (store_term target_pre targ )
  **  (sll_term_list check_list l )
.

Definition check_list_gen_partial_solve_wit_6_pure := 
forall (target_pre: Z) (thm_pre: Z) (targ: term) (theo: term) (check_list: Z) (l: (@list term)) (retval_3: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_3 = 0) |] 
  &&  [| (retval_3 = (term_alpha_eqn (theo) (targ))) |] 
  &&  [| (thm_pre <> 0) |] 
  &&  [| (target_pre <> 0) |] 
  &&  [| (thm_pre <> 0) |]
  &&  ((&((retval_2)  # "term_list" ->ₛ "element")) # Ptr  |-> 0)
  **  ((&((retval_2)  # "term_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "new_node" ) )) # Ptr  |-> retval_2)
  **  (store_imply_res retval (sep_impl (theo)) )
  **  ((( &( "p" ) )) # Ptr  |-> retval)
  **  (store_term target_pre targ )
  **  ((( &( "target" ) )) # Ptr  |-> target_pre)
  **  ((( &( "check_list" ) )) # Ptr  |-> check_list)
  **  (sll_term_list check_list l )
  **  ((( &( "tail_ptr" ) )) # Ptr  |-> ( &( "check_list" ) ))
  **  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
|--
  [| (retval <> 0) |]
.

Definition check_list_gen_partial_solve_wit_6_aux := 
forall (target_pre: Z) (thm_pre: Z) (targ: term) (theo: term) (check_list: Z) (l: (@list term)) (retval: Z) (retval_2: Z) (retval_3: Z) ,
  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval = (term_alpha_eqn (theo) (targ))) |] 
  &&  [| (thm_pre <> 0) |] 
  &&  [| (target_pre <> 0) |] 
  &&  [| (thm_pre <> 0) |]
  &&  ((&((retval_3)  # "term_list" ->ₛ "element")) # Ptr  |-> 0)
  **  ((&((retval_3)  # "term_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_imply_res retval_2 (sep_impl (theo)) )
  **  (store_term target_pre targ )
  **  (sll_term_list check_list l )
|--
  [| (retval_2 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval = (term_alpha_eqn (theo) (targ))) |] 
  &&  [| (thm_pre <> 0) |] 
  &&  [| (target_pre <> 0) |] 
  &&  [| (thm_pre <> 0) |]
  &&  (store_imply_res retval_2 (sep_impl (theo)) )
  **  ((&((retval_3)  # "term_list" ->ₛ "element")) # Ptr  |-> 0)
  **  ((&((retval_3)  # "term_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_term target_pre targ )
  **  (sll_term_list check_list l )
.

Definition check_list_gen_partial_solve_wit_6 := check_list_gen_partial_solve_wit_6_pure -> check_list_gen_partial_solve_wit_6_aux.

Definition check_list_gen_partial_solve_wit_7_pure := 
forall (target_pre: Z) (thm_pre: Z) (targ: term) (theo: term) (check_list: Z) (l: (@list term)) (retval_2: Z) (retval: Z) (retval_3: Z) (p_concl_2: Z) (p_assum_2: Z) (p_assum: term) (p_concl: term) ,
  [| ((sep_impl (theo)) = (imply_res_Cont (p_assum) (p_concl))) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| (retval_2 = (term_alpha_eqn (theo) (targ))) |] 
  &&  [| (thm_pre <> 0) |] 
  &&  [| (target_pre <> 0) |] 
  &&  [| (thm_pre <> 0) |]
  &&  ((( &( "p" ) )) # Ptr  |-> retval)
  **  ((&((retval)  # "imply_prop" ->ₛ "assum")) # Ptr  |-> p_assum_2)
  **  (store_term p_assum_2 p_assum )
  **  ((&((retval)  # "imply_prop" ->ₛ "concl")) # Ptr  |-> p_concl_2)
  **  (store_term p_concl_2 p_concl )
  **  ((&((retval_3)  # "term_list" ->ₛ "element")) # Ptr  |-> p_assum_2)
  **  ((&((retval_3)  # "term_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "new_node" ) )) # Ptr  |-> retval_3)
  **  (store_term target_pre targ )
  **  ((( &( "target" ) )) # Ptr  |-> target_pre)
  **  ((( &( "check_list" ) )) # Ptr  |-> retval_3)
  **  (sll_term_list check_list l )
  **  ((( &( "tail_ptr" ) )) # Ptr  |-> &((retval_3)  # "term_list" ->ₛ "next"))
  **  ((( &( "thm" ) )) # Ptr  |-> p_concl_2)
|--
  [| (retval <> 0) |] 
  &&  [| ((sep_impl (theo)) = (imply_res_Cont (p_assum) (p_concl))) |]
.

Definition check_list_gen_partial_solve_wit_7_aux := 
forall (target_pre: Z) (thm_pre: Z) (targ: term) (theo: term) (check_list: Z) (l: (@list term)) (retval: Z) (retval_2: Z) (retval_3: Z) (p_concl: Z) (p_assum: Z) (p_assum_2: term) (p_concl_2: term) ,
  [| ((sep_impl (theo)) = (imply_res_Cont (p_assum_2) (p_concl_2))) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval = (term_alpha_eqn (theo) (targ))) |] 
  &&  [| (thm_pre <> 0) |] 
  &&  [| (target_pre <> 0) |] 
  &&  [| (thm_pre <> 0) |]
  &&  ((&((retval_2)  # "imply_prop" ->ₛ "assum")) # Ptr  |-> p_assum)
  **  (store_term p_assum p_assum_2 )
  **  ((&((retval_2)  # "imply_prop" ->ₛ "concl")) # Ptr  |-> p_concl)
  **  (store_term p_concl p_concl_2 )
  **  ((&((retval_3)  # "term_list" ->ₛ "element")) # Ptr  |-> p_assum)
  **  ((&((retval_3)  # "term_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_term target_pre targ )
  **  (sll_term_list check_list l )
|--
  [| (retval_2 <> 0) |] 
  &&  [| ((sep_impl (theo)) = (imply_res_Cont (p_assum_2) (p_concl_2))) |] 
  &&  [| ((sep_impl (theo)) = (imply_res_Cont (p_assum_2) (p_concl_2))) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval = (term_alpha_eqn (theo) (targ))) |] 
  &&  [| (thm_pre <> 0) |] 
  &&  [| (target_pre <> 0) |] 
  &&  [| (thm_pre <> 0) |]
  &&  ((&((retval_2)  # "imply_prop" ->ₛ "assum")) # Ptr  |-> p_assum)
  **  (store_term p_assum p_assum_2 )
  **  ((&((retval_2)  # "imply_prop" ->ₛ "concl")) # Ptr  |-> p_concl)
  **  (store_term p_concl p_concl_2 )
  **  ((&((retval_3)  # "term_list" ->ₛ "element")) # Ptr  |-> p_assum)
  **  ((&((retval_3)  # "term_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_term target_pre targ )
  **  (sll_term_list check_list l )
.

Definition check_list_gen_partial_solve_wit_7 := check_list_gen_partial_solve_wit_7_pure -> check_list_gen_partial_solve_wit_7_aux.

Definition check_list_gen_partial_solve_wit_8 := 
forall (target_pre: Z) (thm_pre: Z) (targ: term) (theo: term) (check_list: Z) (l: (@list term)) (retval: Z) (retval_2: Z) (retval_3: Z) (p_assum: Z) (p_assum_2: term) (p_concl: term) (y: Z) (z: Z) ,
  [| ((sep_impl (theo)) = (imply_res_Cont (p_assum_2) (p_concl))) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval = (term_alpha_eqn (theo) (targ))) |] 
  &&  [| (thm_pre <> 0) |] 
  &&  [| (target_pre <> 0) |] 
  &&  [| (thm_pre <> 0) |]
  &&  (store_ImplyProp retval_2 y z p_assum_2 p_concl )
  **  ((&((retval_3)  # "term_list" ->ₛ "element")) # Ptr  |-> p_assum)
  **  ((&((retval_3)  # "term_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_term target_pre targ )
  **  (sll_term_list check_list l )
|--
  [| ((sep_impl (theo)) = (imply_res_Cont (p_assum_2) (p_concl))) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval = (term_alpha_eqn (theo) (targ))) |] 
  &&  [| (thm_pre <> 0) |] 
  &&  [| (target_pre <> 0) |] 
  &&  [| (thm_pre <> 0) |]
  &&  (store_ImplyProp retval_2 y z p_assum_2 p_concl )
  **  ((&((retval_3)  # "term_list" ->ₛ "element")) # Ptr  |-> p_assum)
  **  ((&((retval_3)  # "term_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_term target_pre targ )
  **  (sll_term_list check_list l )
.

Definition check_list_gen_which_implies_wit_1 := 
forall (check_list: Z) ,
  [| (check_list = 0) |]
  &&  emp
|--
  (sll_term_list check_list nil )
.

Definition check_list_gen_which_implies_wit_2 := 
forall (theo: term) (p: Z) ,
  [| (p <> 0) |]
  &&  (store_imply_res p (sep_impl (theo)) )
|--
  EX (p_concl: Z)  (p_assum: Z)  (p_assum_2: term)  (p_concl_2: term) ,
  [| ((sep_impl (theo)) = (imply_res_Cont (p_assum_2) (p_concl_2))) |]
  &&  ((&((p)  # "imply_prop" ->ₛ "assum")) # Ptr  |-> p_assum)
  **  (store_term p_assum p_assum_2 )
  **  ((&((p)  # "imply_prop" ->ₛ "concl")) # Ptr  |-> p_concl)
  **  (store_term p_concl p_concl_2 )
.

Definition check_list_gen_which_implies_wit_3 := 
forall (theo: term) (p_concl: term) (p_assum: term) (p: Z) (p_assum_2: Z) (p_concl_2: Z) ,
  [| (p <> 0) |] 
  &&  [| ((sep_impl (theo)) = (imply_res_Cont (p_assum) (p_concl))) |]
  &&  ((&((p)  # "imply_prop" ->ₛ "assum")) # Ptr  |-> p_assum_2)
  **  (store_term p_assum_2 p_assum )
  **  ((&((p)  # "imply_prop" ->ₛ "concl")) # Ptr  |-> p_concl_2)
  **  (store_term p_concl_2 p_concl )
|--
  EX (y: Z)  (z: Z) ,
  (store_ImplyProp p y z p_assum p_concl )
.

(*----- Function thm_apply -----*)

Definition thm_apply_safety_wit_1 := 
forall (goal_pre: Z) (lis_pre: Z) (thm_pre: Z) (g: term) (l: (@list var_sub)) (t: term) (retval: Z) (retval_2: Z) (v: Z) (res_type: Z) ,
  [| (res_type = 0) |] 
  &&  [| (v = 0) |] 
  &&  [| (retval_2 <> 0) |]
  &&  ((( &( "res" ) )) # Ptr  |-> retval_2)
  **  ((&((retval_2)  # "solve_res" ->ₛ "type")) # Int  |-> res_type)
  **  ((&((retval_2)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> v)
  **  (sll_var_sub_list lis_pre l )
  **  (store_term_res retval (thm_subst (t) (l)) )
  **  ((( &( "thm_ins" ) )) # Ptr  |-> retval)
  **  ((( &( "goal" ) )) # Ptr  |-> goal_pre)
  **  ((( &( "lis" ) )) # Ptr  |-> lis_pre)
  **  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
  **  (store_term goal_pre g )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition thm_apply_safety_wit_2 := 
forall (goal_pre: Z) (lis_pre: Z) (thm_pre: Z) (g: term) (l: (@list var_sub)) (t: term) (retval: Z) (retval_2: Z) (v: Z) (res_type: Z) ,
  [| (retval = 0) |] 
  &&  [| (res_type = 0) |] 
  &&  [| (v = 0) |] 
  &&  [| (retval_2 <> 0) |]
  &&  ((( &( "res" ) )) # Ptr  |-> retval_2)
  **  ((&((retval_2)  # "solve_res" ->ₛ "type")) # Int  |-> res_type)
  **  ((&((retval_2)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> v)
  **  (sll_var_sub_list lis_pre l )
  **  (store_term_res retval (thm_subst (t) (l)) )
  **  ((( &( "thm_ins" ) )) # Ptr  |-> retval)
  **  ((( &( "goal" ) )) # Ptr  |-> goal_pre)
  **  ((( &( "lis" ) )) # Ptr  |-> lis_pre)
  **  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
  **  (store_term goal_pre g )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition thm_apply_safety_wit_3 := 
forall (goal_pre: Z) (lis_pre: Z) (thm_pre: Z) (g: term) (l: (@list var_sub)) (t: term) (retval: Z) (retval_2: Z) (v: Z) (res_type: Z) ,
  [| (retval = 0) |] 
  &&  [| (res_type = 0) |] 
  &&  [| (v = 0) |] 
  &&  [| (retval_2 <> 0) |]
  &&  ((( &( "res" ) )) # Ptr  |-> retval_2)
  **  ((&((retval_2)  # "solve_res" ->ₛ "type")) # Int  |-> 0)
  **  ((&((retval_2)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> v)
  **  (sll_var_sub_list lis_pre l )
  **  (store_term_res retval (thm_subst (t) (l)) )
  **  ((( &( "thm_ins" ) )) # Ptr  |-> retval)
  **  ((( &( "goal" ) )) # Ptr  |-> goal_pre)
  **  ((( &( "lis" ) )) # Ptr  |-> lis_pre)
  **  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
  **  (store_term goal_pre g )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition thm_apply_safety_wit_4 := 
forall (goal_pre: Z) (lis_pre: Z) (thm_pre: Z) (g: term) (l: (@list var_sub)) (retval_2: Z) (retval_3: Z) (v: Z) (res_type: Z) (tst: term) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = (term_alpha_eqn (tst) (g))) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (res_type = 0) |] 
  &&  [| (v = 0) |] 
  &&  [| (retval_3 <> 0) |]
  &&  (store_term retval_2 tst )
  **  (store_term goal_pre g )
  **  ((( &( "thm_ins" ) )) # Ptr  |-> retval_2)
  **  ((( &( "res" ) )) # Ptr  |-> retval_3)
  **  ((&((retval_3)  # "solve_res" ->ₛ "type")) # Int  |-> res_type)
  **  ((&((retval_3)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> v)
  **  (sll_var_sub_list lis_pre l )
  **  ((( &( "goal" ) )) # Ptr  |-> goal_pre)
  **  ((( &( "lis" ) )) # Ptr  |-> lis_pre)
  **  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition thm_apply_safety_wit_5 := 
forall (goal_pre: Z) (lis_pre: Z) (thm_pre: Z) (g: term) (l: (@list var_sub)) (retval_2: Z) (retval_3: Z) (v: Z) (res_type: Z) (tst: term) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = (term_alpha_eqn (tst) (g))) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (res_type = 0) |] 
  &&  [| (v = 0) |] 
  &&  [| (retval_3 <> 0) |]
  &&  (store_term retval_2 tst )
  **  (store_term goal_pre g )
  **  ((( &( "thm_ins" ) )) # Ptr  |-> retval_2)
  **  ((( &( "res" ) )) # Ptr  |-> retval_3)
  **  ((&((retval_3)  # "solve_res" ->ₛ "type")) # Int  |-> 0)
  **  ((&((retval_3)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> v)
  **  (sll_var_sub_list lis_pre l )
  **  ((( &( "goal" ) )) # Ptr  |-> goal_pre)
  **  ((( &( "lis" ) )) # Ptr  |-> lis_pre)
  **  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition thm_apply_safety_wit_6 := 
forall (goal_pre: Z) (lis_pre: Z) (thm_pre: Z) (g: term) (l: (@list var_sub)) (retval_2: Z) (retval_3: Z) (v: Z) (res_type: Z) (tst: term) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = (term_alpha_eqn (tst) (g))) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (res_type = 0) |] 
  &&  [| (v = 0) |] 
  &&  [| (retval_3 <> 0) |]
  &&  (store_term retval_2 tst )
  **  (store_term goal_pre g )
  **  ((( &( "thm_ins" ) )) # Ptr  |-> retval_2)
  **  ((( &( "res" ) )) # Ptr  |-> retval_3)
  **  ((&((retval_3)  # "solve_res" ->ₛ "type")) # Int  |-> res_type)
  **  ((&((retval_3)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> v)
  **  (sll_var_sub_list lis_pre l )
  **  ((( &( "goal" ) )) # Ptr  |-> goal_pre)
  **  ((( &( "lis" ) )) # Ptr  |-> lis_pre)
  **  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition thm_apply_return_wit_1_1 := 
forall (goal_pre: Z) (lis_pre: Z) (g: term) (l: (@list var_sub)) (t: term) (retval_3: Z) (retval: Z) (v: Z) (res_type: Z) (tst: term) (retval_4: Z) (v_2: Z) (retval_2: Z) ,
  [| (v_2 = 0) |] 
  &&  [| (retval_4 = 0) |] 
  &&  [| (retval_4 = (term_alpha_eqn (tst) (g))) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (res_type = 0) |] 
  &&  [| (v = 0) |] 
  &&  [| (retval <> 0) |]
  &&  (store_term retval_3 tst )
  **  (store_term goal_pre g )
  **  (sll_term_list retval_2 (gen_pre (tst) (g)) )
  **  ((&((retval)  # "solve_res" ->ₛ "d" .ₛ "list")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "solve_res" ->ₛ "type")) # Int  |-> 1)
  **  (sll_var_sub_list lis_pre l )
|--
  (sll_var_sub_list lis_pre l )
  **  (store_term goal_pre g )
  **  (store_solve_res retval (thm_app (t) (l) (g)) )
.

Definition thm_apply_return_wit_1_2 := 
forall (goal_pre: Z) (lis_pre: Z) (g: term) (l: (@list var_sub)) (t: term) (retval_3: Z) (retval: Z) (v: Z) (res_type: Z) (tst: term) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval_2 = (term_alpha_eqn (tst) (g))) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (res_type = 0) |] 
  &&  [| (v = 0) |] 
  &&  [| (retval <> 0) |]
  &&  (store_term retval_3 tst )
  **  (store_term goal_pre g )
  **  ((&((retval)  # "solve_res" ->ₛ "type")) # Int  |-> 0)
  **  ((&((retval)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> 1)
  **  (sll_var_sub_list lis_pre l )
|--
  (sll_var_sub_list lis_pre l )
  **  (store_term goal_pre g )
  **  (store_solve_res retval (thm_app (t) (l) (g)) )
.

Definition thm_apply_return_wit_1_3 := 
forall (goal_pre: Z) (lis_pre: Z) (g: term) (l: (@list var_sub)) (t: term) (retval_2: Z) (retval: Z) (v: Z) (res_type: Z) ,
  [| (retval_2 = 0) |] 
  &&  [| (res_type = 0) |] 
  &&  [| (v = 0) |] 
  &&  [| (retval <> 0) |]
  &&  ((&((retval)  # "solve_res" ->ₛ "type")) # Int  |-> 0)
  **  ((&((retval)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> 0)
  **  (sll_var_sub_list lis_pre l )
  **  (store_term_res retval_2 (thm_subst (t) (l)) )
  **  (store_term goal_pre g )
|--
  (sll_var_sub_list lis_pre l )
  **  (store_term goal_pre g )
  **  (store_solve_res retval (thm_app (t) (l) (g)) )
.

Definition thm_apply_partial_solve_wit_1 := 
forall (goal_pre: Z) (lis_pre: Z) (thm_pre: Z) (g: term) (l: (@list var_sub)) (t: term) ,
  (store_term thm_pre t )
  **  (sll_var_sub_list lis_pre l )
  **  (store_term goal_pre g )
|--
  (store_term thm_pre t )
  **  (sll_var_sub_list lis_pre l )
  **  (store_term goal_pre g )
.

Definition thm_apply_partial_solve_wit_2 := 
forall (goal_pre: Z) (lis_pre: Z) (g: term) (l: (@list var_sub)) (t: term) (retval: Z) ,
  (sll_var_sub_list lis_pre l )
  **  (store_term_res retval (thm_subst (t) (l)) )
  **  (store_term goal_pre g )
|--
  (sll_var_sub_list lis_pre l )
  **  (store_term_res retval (thm_subst (t) (l)) )
  **  (store_term goal_pre g )
.

Definition thm_apply_partial_solve_wit_3 := 
forall (goal_pre: Z) (lis_pre: Z) (g: term) (l: (@list var_sub)) (t: term) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |]
  &&  (store_solve_res retval_2 (SRBool (0)) )
  **  (sll_var_sub_list lis_pre l )
  **  (store_term_res retval (thm_subst (t) (l)) )
  **  (store_term goal_pre g )
|--
  [| (retval_2 <> 0) |]
  &&  (store_solve_res retval_2 (SRBool (0)) )
  **  (sll_var_sub_list lis_pre l )
  **  (store_term_res retval (thm_subst (t) (l)) )
  **  (store_term goal_pre g )
.

Definition thm_apply_partial_solve_wit_4_pure := 
forall (goal_pre: Z) (lis_pre: Z) (thm_pre: Z) (g: term) (l: (@list var_sub)) (t: term) (retval: Z) (retval_2: Z) (v: Z) (res_type: Z) ,
  [| (retval <> 0) |] 
  &&  [| (res_type = 0) |] 
  &&  [| (v = 0) |] 
  &&  [| (retval_2 <> 0) |]
  &&  ((( &( "res" ) )) # Ptr  |-> retval_2)
  **  ((&((retval_2)  # "solve_res" ->ₛ "type")) # Int  |-> res_type)
  **  ((&((retval_2)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> v)
  **  (sll_var_sub_list lis_pre l )
  **  (store_term_res retval (thm_subst (t) (l)) )
  **  ((( &( "thm_ins" ) )) # Ptr  |-> retval)
  **  ((( &( "goal" ) )) # Ptr  |-> goal_pre)
  **  ((( &( "lis" ) )) # Ptr  |-> lis_pre)
  **  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
  **  (store_term goal_pre g )
|--
  [| (retval <> 0) |]
.

Definition thm_apply_partial_solve_wit_4_aux := 
forall (goal_pre: Z) (lis_pre: Z) (g: term) (l: (@list var_sub)) (t: term) (retval: Z) (retval_2: Z) (v: Z) (res_type: Z) ,
  [| (retval <> 0) |] 
  &&  [| (res_type = 0) |] 
  &&  [| (v = 0) |] 
  &&  [| (retval_2 <> 0) |]
  &&  ((&((retval_2)  # "solve_res" ->ₛ "type")) # Int  |-> res_type)
  **  ((&((retval_2)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> v)
  **  (sll_var_sub_list lis_pre l )
  **  (store_term_res retval (thm_subst (t) (l)) )
  **  (store_term goal_pre g )
|--
  [| (retval <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (res_type = 0) |] 
  &&  [| (v = 0) |] 
  &&  [| (retval_2 <> 0) |]
  &&  (store_term_res retval (thm_subst (t) (l)) )
  **  ((&((retval_2)  # "solve_res" ->ₛ "type")) # Int  |-> res_type)
  **  ((&((retval_2)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> v)
  **  (sll_var_sub_list lis_pre l )
  **  (store_term goal_pre g )
.

Definition thm_apply_partial_solve_wit_4 := thm_apply_partial_solve_wit_4_pure -> thm_apply_partial_solve_wit_4_aux.

Definition thm_apply_partial_solve_wit_5 := 
forall (goal_pre: Z) (lis_pre: Z) (g: term) (l: (@list var_sub)) (retval: Z) (retval_2: Z) (v: Z) (res_type: Z) (tst: term) ,
  [| (retval <> 0) |] 
  &&  [| (res_type = 0) |] 
  &&  [| (v = 0) |] 
  &&  [| (retval_2 <> 0) |]
  &&  (store_term retval tst )
  **  ((&((retval_2)  # "solve_res" ->ₛ "type")) # Int  |-> res_type)
  **  ((&((retval_2)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> v)
  **  (sll_var_sub_list lis_pre l )
  **  (store_term goal_pre g )
|--
  [| (retval <> 0) |] 
  &&  [| (res_type = 0) |] 
  &&  [| (v = 0) |] 
  &&  [| (retval_2 <> 0) |]
  &&  (store_term retval tst )
  **  (store_term goal_pre g )
  **  ((&((retval_2)  # "solve_res" ->ₛ "type")) # Int  |-> res_type)
  **  ((&((retval_2)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> v)
  **  (sll_var_sub_list lis_pre l )
.

Definition thm_apply_partial_solve_wit_6_pure := 
forall (goal_pre: Z) (lis_pre: Z) (thm_pre: Z) (g: term) (l: (@list var_sub)) (retval_2: Z) (retval_3: Z) (v: Z) (res_type: Z) (tst: term) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = (term_alpha_eqn (tst) (g))) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (res_type = 0) |] 
  &&  [| (v = 0) |] 
  &&  [| (retval_3 <> 0) |]
  &&  (store_term retval_2 tst )
  **  (store_term goal_pre g )
  **  ((( &( "thm_ins" ) )) # Ptr  |-> retval_2)
  **  ((( &( "res" ) )) # Ptr  |-> retval_3)
  **  ((&((retval_3)  # "solve_res" ->ₛ "type")) # Int  |-> 1)
  **  ((&((retval_3)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> v)
  **  (sll_var_sub_list lis_pre l )
  **  ((( &( "goal" ) )) # Ptr  |-> goal_pre)
  **  ((( &( "lis" ) )) # Ptr  |-> lis_pre)
  **  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
|--
  [| (v = 0) |]
.

Definition thm_apply_partial_solve_wit_6_aux := 
forall (goal_pre: Z) (lis_pre: Z) (g: term) (l: (@list var_sub)) (retval: Z) (retval_2: Z) (v: Z) (res_type: Z) (tst: term) (retval_3: Z) ,
  [| (retval_3 = 0) |] 
  &&  [| (retval_3 = (term_alpha_eqn (tst) (g))) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (res_type = 0) |] 
  &&  [| (v = 0) |] 
  &&  [| (retval_2 <> 0) |]
  &&  (store_term retval tst )
  **  (store_term goal_pre g )
  **  ((&((retval_2)  # "solve_res" ->ₛ "type")) # Int  |-> 1)
  **  ((&((retval_2)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> v)
  **  (sll_var_sub_list lis_pre l )
|--
  [| (v = 0) |] 
  &&  [| (retval_3 = 0) |] 
  &&  [| (retval_3 = (term_alpha_eqn (tst) (g))) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (res_type = 0) |] 
  &&  [| (v = 0) |] 
  &&  [| (retval_2 <> 0) |]
  &&  ((&((retval_2)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> v)
  **  (store_term retval tst )
  **  (store_term goal_pre g )
  **  ((&((retval_2)  # "solve_res" ->ₛ "type")) # Int  |-> 1)
  **  (sll_var_sub_list lis_pre l )
.

Definition thm_apply_partial_solve_wit_6 := thm_apply_partial_solve_wit_6_pure -> thm_apply_partial_solve_wit_6_aux.

Definition thm_apply_partial_solve_wit_7 := 
forall (goal_pre: Z) (lis_pre: Z) (g: term) (l: (@list var_sub)) (retval: Z) (retval_2: Z) (v: Z) (res_type: Z) (tst: term) (retval_3: Z) (v_2: Z) ,
  [| (v_2 = 0) |] 
  &&  [| (retval_3 = 0) |] 
  &&  [| (retval_3 = (term_alpha_eqn (tst) (g))) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (res_type = 0) |] 
  &&  [| (v = 0) |] 
  &&  [| (retval_2 <> 0) |]
  &&  ((&((retval_2)  # "solve_res" ->ₛ "d" .ₛ "list")) # Ptr  |-> v_2)
  **  (store_term retval tst )
  **  (store_term goal_pre g )
  **  ((&((retval_2)  # "solve_res" ->ₛ "type")) # Int  |-> 1)
  **  (sll_var_sub_list lis_pre l )
|--
  [| (v_2 = 0) |] 
  &&  [| (retval_3 = 0) |] 
  &&  [| (retval_3 = (term_alpha_eqn (tst) (g))) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (res_type = 0) |] 
  &&  [| (v = 0) |] 
  &&  [| (retval_2 <> 0) |]
  &&  (store_term retval tst )
  **  (store_term goal_pre g )
  **  ((&((retval_2)  # "solve_res" ->ₛ "d" .ₛ "list")) # Ptr  |-> v_2)
  **  ((&((retval_2)  # "solve_res" ->ₛ "type")) # Int  |-> 1)
  **  (sll_var_sub_list lis_pre l )
.

Definition thm_apply_which_implies_wit_1 := 
forall (res: Z) ,
  (store_solve_res res (SRBool (0)) )
|--
  EX (v: Z)  (res_type: Z) ,
  [| (res_type = 0) |] 
  &&  [| (v = 0) |]
  &&  ((&((res)  # "solve_res" ->ₛ "type")) # Int  |-> res_type)
  **  ((&((res)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> v)
.

Definition thm_apply_which_implies_wit_2 := 
forall (l: (@list var_sub)) (t: term) (thm_ins: Z) ,
  [| (thm_ins <> 0) |]
  &&  (store_term_res thm_ins (thm_subst (t) (l)) )
|--
  EX (tst: term) ,
  (store_term thm_ins tst )
.

Definition thm_apply_which_implies_wit_3 := 
forall (res: Z) (v_2: Z) ,
  [| (v_2 = 0) |]
  &&  ((&((res)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> v_2)
|--
  EX (v: Z) ,
  [| (v = 0) |]
  &&  ((&((res)  # "solve_res" ->ₛ "d" .ₛ "list")) # Ptr  |-> v)
.

Module Type VC_Correct.

Axiom proof_of_sub_thm_safety_wit_1 : sub_thm_safety_wit_1.
Axiom proof_of_sub_thm_safety_wit_2 : sub_thm_safety_wit_2.
Axiom proof_of_sub_thm_safety_wit_3 : sub_thm_safety_wit_3.
Axiom proof_of_sub_thm_return_wit_1 : sub_thm_return_wit_1.
Axiom proof_of_sub_thm_return_wit_2 : sub_thm_return_wit_2.
Axiom proof_of_sub_thm_return_wit_3 : sub_thm_return_wit_3.
Axiom proof_of_sub_thm_partial_solve_wit_1_pure : sub_thm_partial_solve_wit_1_pure.
Axiom proof_of_sub_thm_partial_solve_wit_1 : sub_thm_partial_solve_wit_1.
Axiom proof_of_sub_thm_partial_solve_wit_2_pure : sub_thm_partial_solve_wit_2_pure.
Axiom proof_of_sub_thm_partial_solve_wit_2 : sub_thm_partial_solve_wit_2.
Axiom proof_of_sub_thm_partial_solve_wit_3_pure : sub_thm_partial_solve_wit_3_pure.
Axiom proof_of_sub_thm_partial_solve_wit_3 : sub_thm_partial_solve_wit_3.
Axiom proof_of_sub_thm_partial_solve_wit_4 : sub_thm_partial_solve_wit_4.
Axiom proof_of_sub_thm_which_implies_wit_1 : sub_thm_which_implies_wit_1.
Axiom proof_of_sub_thm_which_implies_wit_2 : sub_thm_which_implies_wit_2.
Axiom proof_of_separate_imply_safety_wit_1 : separate_imply_safety_wit_1.
Axiom proof_of_separate_imply_safety_wit_2 : separate_imply_safety_wit_2.
Axiom proof_of_separate_imply_safety_wit_3 : separate_imply_safety_wit_3.
Axiom proof_of_separate_imply_safety_wit_4 : separate_imply_safety_wit_4.
Axiom proof_of_separate_imply_safety_wit_5 : separate_imply_safety_wit_5.
Axiom proof_of_separate_imply_safety_wit_6 : separate_imply_safety_wit_6.
Axiom proof_of_separate_imply_safety_wit_7 : separate_imply_safety_wit_7.
Axiom proof_of_separate_imply_safety_wit_8 : separate_imply_safety_wit_8.
Axiom proof_of_separate_imply_return_wit_1 : separate_imply_return_wit_1.
Axiom proof_of_separate_imply_return_wit_2 : separate_imply_return_wit_2.
Axiom proof_of_separate_imply_return_wit_3 : separate_imply_return_wit_3.
Axiom proof_of_separate_imply_return_wit_4 : separate_imply_return_wit_4.
Axiom proof_of_separate_imply_return_wit_5 : separate_imply_return_wit_5.
Axiom proof_of_separate_imply_partial_solve_wit_1 : separate_imply_partial_solve_wit_1.
Axiom proof_of_separate_imply_partial_solve_wit_2_pure : separate_imply_partial_solve_wit_2_pure.
Axiom proof_of_separate_imply_partial_solve_wit_2 : separate_imply_partial_solve_wit_2.
Axiom proof_of_separate_imply_partial_solve_wit_3 : separate_imply_partial_solve_wit_3.
Axiom proof_of_separate_imply_partial_solve_wit_4_pure : separate_imply_partial_solve_wit_4_pure.
Axiom proof_of_separate_imply_partial_solve_wit_4 : separate_imply_partial_solve_wit_4.
Axiom proof_of_separate_imply_partial_solve_wit_5 : separate_imply_partial_solve_wit_5.
Axiom proof_of_separate_imply_partial_solve_wit_6_pure : separate_imply_partial_solve_wit_6_pure.
Axiom proof_of_separate_imply_partial_solve_wit_6 : separate_imply_partial_solve_wit_6.
Axiom proof_of_separate_imply_partial_solve_wit_7 : separate_imply_partial_solve_wit_7.
Axiom proof_of_separate_imply_which_implies_wit_1 : separate_imply_which_implies_wit_1.
Axiom proof_of_separate_imply_which_implies_wit_2 : separate_imply_which_implies_wit_2.
Axiom proof_of_separate_imply_which_implies_wit_3 : separate_imply_which_implies_wit_3.
Axiom proof_of_separate_imply_which_implies_wit_4 : separate_imply_which_implies_wit_4.
Axiom proof_of_separate_imply_which_implies_wit_5 : separate_imply_which_implies_wit_5.
Axiom proof_of_separate_imply_which_implies_wit_6 : separate_imply_which_implies_wit_6.
Axiom proof_of_check_list_gen_safety_wit_1 : check_list_gen_safety_wit_1.
Axiom proof_of_check_list_gen_safety_wit_2 : check_list_gen_safety_wit_2.
Axiom proof_of_check_list_gen_safety_wit_3 : check_list_gen_safety_wit_3.
Axiom proof_of_check_list_gen_safety_wit_4 : check_list_gen_safety_wit_4.
Axiom proof_of_check_list_gen_safety_wit_5 : check_list_gen_safety_wit_5.
Axiom proof_of_check_list_gen_safety_wit_6 : check_list_gen_safety_wit_6.
Axiom proof_of_check_list_gen_safety_wit_7 : check_list_gen_safety_wit_7.
Axiom proof_of_check_list_gen_safety_wit_8 : check_list_gen_safety_wit_8.
Axiom proof_of_check_list_gen_safety_wit_9 : check_list_gen_safety_wit_9.
Axiom proof_of_check_list_gen_safety_wit_10 : check_list_gen_safety_wit_10.
Axiom proof_of_check_list_gen_entail_wit_1 : check_list_gen_entail_wit_1.
Axiom proof_of_check_list_gen_entail_wit_2 : check_list_gen_entail_wit_2.
Axiom proof_of_check_list_gen_return_wit_1 : check_list_gen_return_wit_1.
Axiom proof_of_check_list_gen_return_wit_2_1 : check_list_gen_return_wit_2_1.
Axiom proof_of_check_list_gen_return_wit_2_2 : check_list_gen_return_wit_2_2.
Axiom proof_of_check_list_gen_return_wit_3 : check_list_gen_return_wit_3.
Axiom proof_of_check_list_gen_partial_solve_wit_1_pure : check_list_gen_partial_solve_wit_1_pure.
Axiom proof_of_check_list_gen_partial_solve_wit_1 : check_list_gen_partial_solve_wit_1.
Axiom proof_of_check_list_gen_partial_solve_wit_2 : check_list_gen_partial_solve_wit_2.
Axiom proof_of_check_list_gen_partial_solve_wit_3 : check_list_gen_partial_solve_wit_3.
Axiom proof_of_check_list_gen_partial_solve_wit_4 : check_list_gen_partial_solve_wit_4.
Axiom proof_of_check_list_gen_partial_solve_wit_5 : check_list_gen_partial_solve_wit_5.
Axiom proof_of_check_list_gen_partial_solve_wit_6_pure : check_list_gen_partial_solve_wit_6_pure.
Axiom proof_of_check_list_gen_partial_solve_wit_6 : check_list_gen_partial_solve_wit_6.
Axiom proof_of_check_list_gen_partial_solve_wit_7_pure : check_list_gen_partial_solve_wit_7_pure.
Axiom proof_of_check_list_gen_partial_solve_wit_7 : check_list_gen_partial_solve_wit_7.
Axiom proof_of_check_list_gen_partial_solve_wit_8 : check_list_gen_partial_solve_wit_8.
Axiom proof_of_check_list_gen_which_implies_wit_1 : check_list_gen_which_implies_wit_1.
Axiom proof_of_check_list_gen_which_implies_wit_2 : check_list_gen_which_implies_wit_2.
Axiom proof_of_check_list_gen_which_implies_wit_3 : check_list_gen_which_implies_wit_3.
Axiom proof_of_thm_apply_safety_wit_1 : thm_apply_safety_wit_1.
Axiom proof_of_thm_apply_safety_wit_2 : thm_apply_safety_wit_2.
Axiom proof_of_thm_apply_safety_wit_3 : thm_apply_safety_wit_3.
Axiom proof_of_thm_apply_safety_wit_4 : thm_apply_safety_wit_4.
Axiom proof_of_thm_apply_safety_wit_5 : thm_apply_safety_wit_5.
Axiom proof_of_thm_apply_safety_wit_6 : thm_apply_safety_wit_6.
Axiom proof_of_thm_apply_return_wit_1_1 : thm_apply_return_wit_1_1.
Axiom proof_of_thm_apply_return_wit_1_2 : thm_apply_return_wit_1_2.
Axiom proof_of_thm_apply_return_wit_1_3 : thm_apply_return_wit_1_3.
Axiom proof_of_thm_apply_partial_solve_wit_1 : thm_apply_partial_solve_wit_1.
Axiom proof_of_thm_apply_partial_solve_wit_2 : thm_apply_partial_solve_wit_2.
Axiom proof_of_thm_apply_partial_solve_wit_3 : thm_apply_partial_solve_wit_3.
Axiom proof_of_thm_apply_partial_solve_wit_4_pure : thm_apply_partial_solve_wit_4_pure.
Axiom proof_of_thm_apply_partial_solve_wit_4 : thm_apply_partial_solve_wit_4.
Axiom proof_of_thm_apply_partial_solve_wit_5 : thm_apply_partial_solve_wit_5.
Axiom proof_of_thm_apply_partial_solve_wit_6_pure : thm_apply_partial_solve_wit_6_pure.
Axiom proof_of_thm_apply_partial_solve_wit_6 : thm_apply_partial_solve_wit_6.
Axiom proof_of_thm_apply_partial_solve_wit_7 : thm_apply_partial_solve_wit_7.
Axiom proof_of_thm_apply_which_implies_wit_1 : thm_apply_which_implies_wit_1.
Axiom proof_of_thm_apply_which_implies_wit_2 : thm_apply_which_implies_wit_2.
Axiom proof_of_thm_apply_which_implies_wit_3 : thm_apply_which_implies_wit_3.

End VC_Correct.
