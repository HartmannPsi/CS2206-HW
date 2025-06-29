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

(*----- Function alpha_equiv -----*)

Definition alpha_equiv_safety_wit_1 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) ,
  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition alpha_equiv_safety_wit_2 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) ,
  [| (t1_pre <> 0) |]
  &&  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition alpha_equiv_safety_wit_3 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) ,
  [| (t1_pre = 0) |]
  &&  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition alpha_equiv_safety_wit_4 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) ,
  [| (t2_pre = 0) |] 
  &&  [| (t1_pre <> 0) |]
  &&  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition alpha_equiv_safety_wit_5 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) ,
  [| ((termtypeID (term1)) <> (termtypeID (term2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |]
  &&  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  (store_term' t1_pre term1 )
  **  (store_term' t2_pre term2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition alpha_equiv_safety_wit_6 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) ,
  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |]
  &&  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  (store_term' t1_pre term1 )
  **  (store_term' t2_pre term2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition alpha_equiv_safety_wit_7 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z: Z) (y: Z) (str2: (@list Z)) (str1: (@list Z)) (retval: Z) ,
  [| (retval = (list_Z_cmp (str1) (str2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (term1 = (TermVar (str1))) |] 
  &&  [| (term2 = (TermVar (str2))) |] 
  &&  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) = 0) |]
  &&  (store_string y str1 )
  **  (store_string z str2 )
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> z)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition alpha_equiv_safety_wit_8 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) ,
  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 0) |]
  &&  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  (store_term' t1_pre term1 )
  **  (store_term' t2_pre term2 )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition alpha_equiv_safety_wit_9 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (typ2: const_type) (con2: Z) (typ1: const_type) (con1: Z) ,
  [| ((ctID (typ1)) <> (ctID (typ2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (term1 = (TermConst (typ1) (con1))) |] 
  &&  [| (term2 = (TermConst (typ2) (con2))) |] 
  &&  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 0) |] 
  &&  [| ((termtypeID (term1)) = 1) |]
  &&  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con2)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition alpha_equiv_safety_wit_10 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (typ2: const_type) (con2: Z) (typ1: const_type) (con1: Z) ,
  [| ((ctID (typ1)) = (ctID (typ2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (term1 = (TermConst (typ1) (con1))) |] 
  &&  [| (term2 = (TermConst (typ2) (con2))) |] 
  &&  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 0) |] 
  &&  [| ((termtypeID (term1)) = 1) |]
  &&  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con2)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition alpha_equiv_safety_wit_11 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (typ2: const_type) (con2: Z) (typ1: const_type) (con1: Z) ,
  [| ((ctID (typ1)) <> 0) |] 
  &&  [| ((ctID (typ1)) = (ctID (typ2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (term1 = (TermConst (typ1) (con1))) |] 
  &&  [| (term2 = (TermConst (typ2) (con2))) |] 
  &&  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 0) |] 
  &&  [| ((termtypeID (term1)) = 1) |]
  &&  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con2)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition alpha_equiv_safety_wit_12 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) ,
  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 1) |]
  &&  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  (store_term' t1_pre term1 )
  **  (store_term' t2_pre term2 )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition alpha_equiv_safety_wit_13 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) ,
  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 1) |] 
  &&  [| ((termtypeID (term1)) <> 2) |]
  &&  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  (store_term' t1_pre term1 )
  **  (store_term' t2_pre term2 )
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition alpha_equiv_safety_wit_14 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z2: Z) (z1: Z) (y2: Z) (y1: Z) (qt2: quant_type) (qv2: (@list Z)) (qterm2: term) (qt1: quant_type) (qv1: (@list Z)) (qterm1: term) ,
  [| ((qtID (qt1)) <> (qtID (qt2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (term1 = (TermQuant (qt1) (qv1) (qterm1))) |] 
  &&  [| (term2 = (TermQuant (qt2) (qv2) (qterm2))) |] 
  &&  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 1) |] 
  &&  [| ((termtypeID (term1)) <> 2) |] 
  &&  [| ((termtypeID (term1)) = 3) |]
  &&  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z2)
  **  (store_string y1 qv1 )
  **  (store_term z1 qterm1 )
  **  (store_string y2 qv2 )
  **  (store_term z2 qterm2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition alpha_equiv_safety_wit_15 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z2: Z) (z1: Z) (y2: Z) (y1: Z) (qt2: quant_type) (qv2: (@list Z)) (qterm2: term) (qt1: quant_type) (qv1: (@list Z)) (qterm1: term) (retval: Z) ,
  [| (retval = (list_Z_cmp (qv1) (qv2))) |] 
  &&  [| ((qtID (qt1)) = (qtID (qt2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (term1 = (TermQuant (qt1) (qv1) (qterm1))) |] 
  &&  [| (term2 = (TermQuant (qt2) (qv2) (qterm2))) |] 
  &&  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 1) |] 
  &&  [| ((termtypeID (term1)) <> 2) |] 
  &&  [| ((termtypeID (term1)) = 3) |]
  &&  (store_string y1 qv1 )
  **  (store_string y2 qv2 )
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z2)
  **  (store_term z1 qterm1 )
  **  (store_term z2 qterm2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition alpha_equiv_entail_wit_1 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) ,
  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 1) |] 
  &&  [| ((termtypeID (term1)) <> 2) |] 
  &&  [| ((termtypeID (term1)) <> 3) |]
  &&  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  (store_term' t1_pre term1 )
  **  (store_term' t2_pre term2 )
|--
  [| False |]
  &&  emp
.

Definition alpha_equiv_return_wit_1_1 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z: Z) (y: Z) (str2: (@list Z)) (str1: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = (list_Z_cmp (str1) (str2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (term1 = (TermVar (str1))) |] 
  &&  [| (term2 = (TermVar (str2))) |] 
  &&  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) = 0) |]
  &&  (store_string y str1 )
  **  (store_string z str2 )
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> z)
|--
  [| (0 = (term_alpha_eqn (term1) (term2))) |]
  &&  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
.

Definition alpha_equiv_return_wit_1_2 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z: Z) (y: Z) (str2: (@list Z)) (str1: (@list Z)) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = (list_Z_cmp (str1) (str2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (term1 = (TermVar (str1))) |] 
  &&  [| (term2 = (TermVar (str2))) |] 
  &&  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) = 0) |]
  &&  (store_string y str1 )
  **  (store_string z str2 )
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> z)
|--
  [| (1 = (term_alpha_eqn (term1) (term2))) |]
  &&  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
.

Definition alpha_equiv_return_wit_2 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (typ2: const_type) (con2: Z) (typ1: const_type) (con1: Z) ,
  [| ((ctID (typ1)) <> (ctID (typ2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (term1 = (TermConst (typ1) (con1))) |] 
  &&  [| (term2 = (TermConst (typ2) (con2))) |] 
  &&  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 0) |] 
  &&  [| ((termtypeID (term1)) = 1) |]
  &&  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con2)
|--
  [| (0 = (term_alpha_eqn (term1) (term2))) |]
  &&  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
.

Definition alpha_equiv_return_wit_3_1 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (typ2: const_type) (con2: Z) (typ1: const_type) (con1: Z) ,
  [| (con1 <> con2) |] 
  &&  [| ((ctID (typ1)) = 0) |] 
  &&  [| ((ctID (typ1)) = (ctID (typ2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (term1 = (TermConst (typ1) (con1))) |] 
  &&  [| (term2 = (TermConst (typ2) (con2))) |] 
  &&  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 0) |] 
  &&  [| ((termtypeID (term1)) = 1) |]
  &&  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con2)
|--
  [| (0 = (term_alpha_eqn (term1) (term2))) |]
  &&  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
.

Definition alpha_equiv_return_wit_3_2 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (typ2: const_type) (con2: Z) (typ1: const_type) (con1: Z) ,
  [| (con1 = con2) |] 
  &&  [| ((ctID (typ1)) = 0) |] 
  &&  [| ((ctID (typ1)) = (ctID (typ2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (term1 = (TermConst (typ1) (con1))) |] 
  &&  [| (term2 = (TermConst (typ2) (con2))) |] 
  &&  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 0) |] 
  &&  [| ((termtypeID (term1)) = 1) |]
  &&  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con2)
|--
  [| (1 = (term_alpha_eqn (term1) (term2))) |]
  &&  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
.

Definition alpha_equiv_return_wit_4 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (typ2: const_type) (con2: Z) (typ1: const_type) (con1: Z) ,
  [| ((ctID (typ1)) <> 0) |] 
  &&  [| ((ctID (typ1)) = (ctID (typ2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (term1 = (TermConst (typ1) (con1))) |] 
  &&  [| (term2 = (TermConst (typ2) (con2))) |] 
  &&  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 0) |] 
  &&  [| ((termtypeID (term1)) = 1) |]
  &&  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con2)
|--
  [| (1 = (term_alpha_eqn (term1) (term2))) |]
  &&  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
.

Definition alpha_equiv_return_wit_5_1 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z2: Z) (z1: Z) (y2: Z) (y1: Z) (lt2: term) (rt2: term) (lt1: term) (rt1: term) (retval_2: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = (term_alpha_eqn (rt1) (rt2))) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval_2 = (term_alpha_eqn (lt1) (lt2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (term1 = (TermApply (lt1) (rt1))) |] 
  &&  [| (term2 = (TermApply (lt2) (rt2))) |] 
  &&  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 1) |] 
  &&  [| ((termtypeID (term1)) = 2) |]
  &&  (store_term z1 rt1 )
  **  (store_term z2 rt2 )
  **  (store_term y1 lt1 )
  **  (store_term y2 lt2 )
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z2)
|--
  [| (1 = (term_alpha_eqn (term1) (term2))) |]
  &&  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
.

Definition alpha_equiv_return_wit_5_2 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z2: Z) (z1: Z) (y2: Z) (y1: Z) (lt2: term) (rt2: term) (lt1: term) (rt1: term) (retval_2: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = (term_alpha_eqn (rt1) (rt2))) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval_2 = (term_alpha_eqn (lt1) (lt2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (term1 = (TermApply (lt1) (rt1))) |] 
  &&  [| (term2 = (TermApply (lt2) (rt2))) |] 
  &&  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 1) |] 
  &&  [| ((termtypeID (term1)) = 2) |]
  &&  (store_term z1 rt1 )
  **  (store_term z2 rt2 )
  **  (store_term y1 lt1 )
  **  (store_term y2 lt2 )
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z2)
|--
  [| (0 = (term_alpha_eqn (term1) (term2))) |]
  &&  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
.

Definition alpha_equiv_return_wit_5_3 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z2: Z) (z1: Z) (y2: Z) (y1: Z) (lt2: term) (rt2: term) (lt1: term) (rt1: term) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = (term_alpha_eqn (lt1) (lt2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (term1 = (TermApply (lt1) (rt1))) |] 
  &&  [| (term2 = (TermApply (lt2) (rt2))) |] 
  &&  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 1) |] 
  &&  [| ((termtypeID (term1)) = 2) |]
  &&  (store_term y1 lt1 )
  **  (store_term y2 lt2 )
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z2)
  **  (store_term z1 rt1 )
  **  (store_term z2 rt2 )
|--
  [| (0 = (term_alpha_eqn (term1) (term2))) |]
  &&  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
.

Definition alpha_equiv_return_wit_6 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z2: Z) (z1: Z) (y2: Z) (y1: Z) (qt2: quant_type) (qv2: (@list Z)) (qterm2: term) (qt1: quant_type) (qv1: (@list Z)) (qterm1: term) ,
  [| ((qtID (qt1)) <> (qtID (qt2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (term1 = (TermQuant (qt1) (qv1) (qterm1))) |] 
  &&  [| (term2 = (TermQuant (qt2) (qv2) (qterm2))) |] 
  &&  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 1) |] 
  &&  [| ((termtypeID (term1)) <> 2) |] 
  &&  [| ((termtypeID (term1)) = 3) |]
  &&  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z2)
  **  (store_string y1 qv1 )
  **  (store_term z1 qterm1 )
  **  (store_string y2 qv2 )
  **  (store_term z2 qterm2 )
|--
  [| (0 = (term_alpha_eqn (term1) (term2))) |]
  &&  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
.

Definition alpha_equiv_return_wit_7 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z2: Z) (z1: Z) (y2: Z) (y1: Z) (qt2: quant_type) (qv2: (@list Z)) (qterm2: term) (qt1: quant_type) (qv1: (@list Z)) (qterm1: term) (retval_2: Z) (retval: Z) ,
  [| (retval = (term_alpha_eqn (qterm1) (qterm2))) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| (retval_2 = (list_Z_cmp (qv1) (qv2))) |] 
  &&  [| ((qtID (qt1)) = (qtID (qt2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (term1 = (TermQuant (qt1) (qv1) (qterm1))) |] 
  &&  [| (term2 = (TermQuant (qt2) (qv2) (qterm2))) |] 
  &&  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 1) |] 
  &&  [| ((termtypeID (term1)) <> 2) |] 
  &&  [| ((termtypeID (term1)) = 3) |]
  &&  (store_term z1 qterm1 )
  **  (store_term z2 qterm2 )
  **  (store_string y1 qv1 )
  **  (store_string y2 qv2 )
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z2)
|--
  [| (retval = (term_alpha_eqn (term1) (term2))) |]
  &&  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
.

Definition alpha_equiv_return_wit_8 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z2: Z) (z1: Z) (y2: Z) (y1: Z) (qt2: quant_type) (qv2: (@list Z)) (qterm2: term) (qt1: quant_type) (qv1: (@list Z)) (qterm1: term) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval: Z) ,
  [| (retval = (term_alpha_eqn (qterm1) ((term_subst_v (qv1) (qv2) (qterm2))))) |] 
  &&  [| (retval_4 = retval_3) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (y1 <> 0) |] 
  &&  [| (y2 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval_2 = (list_Z_cmp (qv1) (qv2))) |] 
  &&  [| ((qtID (qt1)) = (qtID (qt2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (term1 = (TermQuant (qt1) (qv1) (qterm1))) |] 
  &&  [| (term2 = (TermQuant (qt2) (qv2) (qterm2))) |] 
  &&  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 1) |] 
  &&  [| ((termtypeID (term1)) <> 2) |] 
  &&  [| ((termtypeID (term1)) = 3) |]
  &&  (store_term z1 qterm1 )
  **  (store_string y1 qv1 )
  **  (store_string y2 qv2 )
  **  (store_term z2 qterm2 )
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z2)
|--
  [| (retval = (term_alpha_eqn (term1) (term2))) |]
  &&  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
.

Definition alpha_equiv_return_wit_9_1 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) ,
  [| (t2_pre = 0) |] 
  &&  [| (t1_pre <> 0) |]
  &&  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
|--
  [| (0 = (term_alpha_eqn (term1) (term2))) |]
  &&  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
.

Definition alpha_equiv_return_wit_9_2 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) ,
  [| (t1_pre = 0) |]
  &&  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
|--
  [| (0 = (term_alpha_eqn (term1) (term2))) |]
  &&  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
.

Definition alpha_equiv_return_wit_10 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) ,
  [| ((termtypeID (term1)) <> (termtypeID (term2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |]
  &&  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  (store_term' t1_pre term1 )
  **  (store_term' t2_pre term2 )
|--
  [| (0 = (term_alpha_eqn (term1) (term2))) |]
  &&  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
.

Definition alpha_equiv_partial_solve_wit_1 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) ,
  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |]
  &&  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
|--
  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |]
  &&  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
.

Definition alpha_equiv_partial_solve_wit_2_pure := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) ,
  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) = 0) |]
  &&  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  (store_term' t1_pre term1 )
  **  (store_term' t2_pre term2 )
|--
  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) = 0) |] 
  &&  [| ((termtypeID (term1)) = (termtypeID (term2))) |]
.

Definition alpha_equiv_partial_solve_wit_2_aux := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) ,
  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) = 0) |]
  &&  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  (store_term' t1_pre term1 )
  **  (store_term' t2_pre term2 )
|--
  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) = 0) |] 
  &&  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) = 0) |]
  &&  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  (store_term' t1_pre term1 )
  **  (store_term' t2_pre term2 )
.

Definition alpha_equiv_partial_solve_wit_2 := alpha_equiv_partial_solve_wit_2_pure -> alpha_equiv_partial_solve_wit_2_aux.

Definition alpha_equiv_partial_solve_wit_3 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z: Z) (y: Z) (str2: (@list Z)) (str1: (@list Z)) ,
  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (term1 = (TermVar (str1))) |] 
  &&  [| (term2 = (TermVar (str2))) |] 
  &&  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) = 0) |]
  &&  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> z)
  **  (store_string y str1 )
  **  (store_string z str2 )
|--
  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (term1 = (TermVar (str1))) |] 
  &&  [| (term2 = (TermVar (str2))) |] 
  &&  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) = 0) |]
  &&  (store_string y str1 )
  **  (store_string z str2 )
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> z)
.

Definition alpha_equiv_partial_solve_wit_4_pure := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) ,
  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 0) |] 
  &&  [| ((termtypeID (term1)) = 1) |]
  &&  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  (store_term' t1_pre term1 )
  **  (store_term' t2_pre term2 )
|--
  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) = 1) |] 
  &&  [| ((termtypeID (term1)) = (termtypeID (term2))) |]
.

Definition alpha_equiv_partial_solve_wit_4_aux := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) ,
  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 0) |] 
  &&  [| ((termtypeID (term1)) = 1) |]
  &&  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  (store_term' t1_pre term1 )
  **  (store_term' t2_pre term2 )
|--
  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) = 1) |] 
  &&  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 0) |] 
  &&  [| ((termtypeID (term1)) = 1) |]
  &&  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  (store_term' t1_pre term1 )
  **  (store_term' t2_pre term2 )
.

Definition alpha_equiv_partial_solve_wit_4 := alpha_equiv_partial_solve_wit_4_pure -> alpha_equiv_partial_solve_wit_4_aux.

Definition alpha_equiv_partial_solve_wit_5_pure := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) ,
  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 1) |] 
  &&  [| ((termtypeID (term1)) = 2) |]
  &&  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  (store_term' t1_pre term1 )
  **  (store_term' t2_pre term2 )
|--
  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) = 2) |] 
  &&  [| ((termtypeID (term1)) = (termtypeID (term2))) |]
.

Definition alpha_equiv_partial_solve_wit_5_aux := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) ,
  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 1) |] 
  &&  [| ((termtypeID (term1)) = 2) |]
  &&  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  (store_term' t1_pre term1 )
  **  (store_term' t2_pre term2 )
|--
  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) = 2) |] 
  &&  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 1) |] 
  &&  [| ((termtypeID (term1)) = 2) |]
  &&  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  (store_term' t1_pre term1 )
  **  (store_term' t2_pre term2 )
.

Definition alpha_equiv_partial_solve_wit_5 := alpha_equiv_partial_solve_wit_5_pure -> alpha_equiv_partial_solve_wit_5_aux.

Definition alpha_equiv_partial_solve_wit_6 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z2: Z) (z1: Z) (y2: Z) (y1: Z) (lt2: term) (rt2: term) (lt1: term) (rt1: term) ,
  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (term1 = (TermApply (lt1) (rt1))) |] 
  &&  [| (term2 = (TermApply (lt2) (rt2))) |] 
  &&  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 1) |] 
  &&  [| ((termtypeID (term1)) = 2) |]
  &&  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z2)
  **  (store_term y1 lt1 )
  **  (store_term z1 rt1 )
  **  (store_term y2 lt2 )
  **  (store_term z2 rt2 )
|--
  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (term1 = (TermApply (lt1) (rt1))) |] 
  &&  [| (term2 = (TermApply (lt2) (rt2))) |] 
  &&  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 1) |] 
  &&  [| ((termtypeID (term1)) = 2) |]
  &&  (store_term y1 lt1 )
  **  (store_term y2 lt2 )
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z2)
  **  (store_term z1 rt1 )
  **  (store_term z2 rt2 )
.

Definition alpha_equiv_partial_solve_wit_7 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z2: Z) (z1: Z) (y2: Z) (y1: Z) (lt2: term) (rt2: term) (lt1: term) (rt1: term) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = (term_alpha_eqn (lt1) (lt2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (term1 = (TermApply (lt1) (rt1))) |] 
  &&  [| (term2 = (TermApply (lt2) (rt2))) |] 
  &&  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 1) |] 
  &&  [| ((termtypeID (term1)) = 2) |]
  &&  (store_term y1 lt1 )
  **  (store_term y2 lt2 )
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z2)
  **  (store_term z1 rt1 )
  **  (store_term z2 rt2 )
|--
  [| (retval <> 0) |] 
  &&  [| (retval = (term_alpha_eqn (lt1) (lt2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (term1 = (TermApply (lt1) (rt1))) |] 
  &&  [| (term2 = (TermApply (lt2) (rt2))) |] 
  &&  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 1) |] 
  &&  [| ((termtypeID (term1)) = 2) |]
  &&  (store_term z1 rt1 )
  **  (store_term z2 rt2 )
  **  (store_term y1 lt1 )
  **  (store_term y2 lt2 )
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z2)
.

Definition alpha_equiv_partial_solve_wit_8_pure := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) ,
  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 1) |] 
  &&  [| ((termtypeID (term1)) <> 2) |] 
  &&  [| ((termtypeID (term1)) = 3) |]
  &&  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  (store_term' t1_pre term1 )
  **  (store_term' t2_pre term2 )
|--
  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) = 3) |] 
  &&  [| ((termtypeID (term1)) = (termtypeID (term2))) |]
.

Definition alpha_equiv_partial_solve_wit_8_aux := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) ,
  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 1) |] 
  &&  [| ((termtypeID (term1)) <> 2) |] 
  &&  [| ((termtypeID (term1)) = 3) |]
  &&  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  (store_term' t1_pre term1 )
  **  (store_term' t2_pre term2 )
|--
  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) = 3) |] 
  &&  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 1) |] 
  &&  [| ((termtypeID (term1)) <> 2) |] 
  &&  [| ((termtypeID (term1)) = 3) |]
  &&  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  (store_term' t1_pre term1 )
  **  (store_term' t2_pre term2 )
.

Definition alpha_equiv_partial_solve_wit_8 := alpha_equiv_partial_solve_wit_8_pure -> alpha_equiv_partial_solve_wit_8_aux.

Definition alpha_equiv_partial_solve_wit_9 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z2: Z) (z1: Z) (y2: Z) (y1: Z) (qt2: quant_type) (qv2: (@list Z)) (qterm2: term) (qt1: quant_type) (qv1: (@list Z)) (qterm1: term) ,
  [| ((qtID (qt1)) = (qtID (qt2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (term1 = (TermQuant (qt1) (qv1) (qterm1))) |] 
  &&  [| (term2 = (TermQuant (qt2) (qv2) (qterm2))) |] 
  &&  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 1) |] 
  &&  [| ((termtypeID (term1)) <> 2) |] 
  &&  [| ((termtypeID (term1)) = 3) |]
  &&  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z2)
  **  (store_string y1 qv1 )
  **  (store_term z1 qterm1 )
  **  (store_string y2 qv2 )
  **  (store_term z2 qterm2 )
|--
  [| ((qtID (qt1)) = (qtID (qt2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (term1 = (TermQuant (qt1) (qv1) (qterm1))) |] 
  &&  [| (term2 = (TermQuant (qt2) (qv2) (qterm2))) |] 
  &&  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 1) |] 
  &&  [| ((termtypeID (term1)) <> 2) |] 
  &&  [| ((termtypeID (term1)) = 3) |]
  &&  (store_string y1 qv1 )
  **  (store_string y2 qv2 )
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z2)
  **  (store_term z1 qterm1 )
  **  (store_term z2 qterm2 )
.

Definition alpha_equiv_partial_solve_wit_10 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z2: Z) (z1: Z) (y2: Z) (y1: Z) (qt2: quant_type) (qv2: (@list Z)) (qterm2: term) (qt1: quant_type) (qv1: (@list Z)) (qterm1: term) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = (list_Z_cmp (qv1) (qv2))) |] 
  &&  [| ((qtID (qt1)) = (qtID (qt2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (term1 = (TermQuant (qt1) (qv1) (qterm1))) |] 
  &&  [| (term2 = (TermQuant (qt2) (qv2) (qterm2))) |] 
  &&  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 1) |] 
  &&  [| ((termtypeID (term1)) <> 2) |] 
  &&  [| ((termtypeID (term1)) = 3) |]
  &&  (store_string y1 qv1 )
  **  (store_string y2 qv2 )
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z2)
  **  (store_term z1 qterm1 )
  **  (store_term z2 qterm2 )
|--
  [| (retval = 0) |] 
  &&  [| (retval = (list_Z_cmp (qv1) (qv2))) |] 
  &&  [| ((qtID (qt1)) = (qtID (qt2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (term1 = (TermQuant (qt1) (qv1) (qterm1))) |] 
  &&  [| (term2 = (TermQuant (qt2) (qv2) (qterm2))) |] 
  &&  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 1) |] 
  &&  [| ((termtypeID (term1)) <> 2) |] 
  &&  [| ((termtypeID (term1)) = 3) |]
  &&  (store_term z1 qterm1 )
  **  (store_term z2 qterm2 )
  **  (store_string y1 qv1 )
  **  (store_string y2 qv2 )
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z2)
.

Definition alpha_equiv_partial_solve_wit_11 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z2: Z) (z1: Z) (y2: Z) (y1: Z) (qt2: quant_type) (qv2: (@list Z)) (qterm2: term) (qt1: quant_type) (qv1: (@list Z)) (qterm1: term) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = (list_Z_cmp (qv1) (qv2))) |] 
  &&  [| ((qtID (qt1)) = (qtID (qt2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (term1 = (TermQuant (qt1) (qv1) (qterm1))) |] 
  &&  [| (term2 = (TermQuant (qt2) (qv2) (qterm2))) |] 
  &&  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 1) |] 
  &&  [| ((termtypeID (term1)) <> 2) |] 
  &&  [| ((termtypeID (term1)) = 3) |]
  &&  (store_string y1 qv1 )
  **  (store_string y2 qv2 )
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z2)
  **  (store_term z1 qterm1 )
  **  (store_term z2 qterm2 )
|--
  [| (retval <> 0) |] 
  &&  [| (retval = (list_Z_cmp (qv1) (qv2))) |] 
  &&  [| ((qtID (qt1)) = (qtID (qt2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (term1 = (TermQuant (qt1) (qv1) (qterm1))) |] 
  &&  [| (term2 = (TermQuant (qt2) (qv2) (qterm2))) |] 
  &&  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 1) |] 
  &&  [| ((termtypeID (term1)) <> 2) |] 
  &&  [| ((termtypeID (term1)) = 3) |]
  &&  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y1)
  **  (store_string y1 qv1 )
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y2)
  **  (store_string y2 qv2 )
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z2)
  **  (store_term z1 qterm1 )
  **  (store_term z2 qterm2 )
.

Definition alpha_equiv_partial_solve_wit_12 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z2: Z) (z1: Z) (y2: Z) (y1: Z) (qt2: quant_type) (qv2: (@list Z)) (qterm2: term) (qt1: quant_type) (qv1: (@list Z)) (qterm1: term) (retval: Z) ,
  [| (y1 <> 0) |] 
  &&  [| (y2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = (list_Z_cmp (qv1) (qv2))) |] 
  &&  [| ((qtID (qt1)) = (qtID (qt2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (term1 = (TermQuant (qt1) (qv1) (qterm1))) |] 
  &&  [| (term2 = (TermQuant (qt2) (qv2) (qterm2))) |] 
  &&  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 1) |] 
  &&  [| ((termtypeID (term1)) <> 2) |] 
  &&  [| ((termtypeID (term1)) = 3) |]
  &&  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y2)
  **  (store_string y1 qv1 )
  **  (store_string y2 qv2 )
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z2)
  **  (store_term z1 qterm1 )
  **  (store_term z2 qterm2 )
|--
  [| (y1 <> 0) |] 
  &&  [| (y2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = (list_Z_cmp (qv1) (qv2))) |] 
  &&  [| ((qtID (qt1)) = (qtID (qt2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (term1 = (TermQuant (qt1) (qv1) (qterm1))) |] 
  &&  [| (term2 = (TermQuant (qt2) (qv2) (qterm2))) |] 
  &&  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 1) |] 
  &&  [| ((termtypeID (term1)) <> 2) |] 
  &&  [| ((termtypeID (term1)) = 3) |]
  &&  (store_term z2 qterm2 )
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y2)
  **  (store_string y1 qv1 )
  **  (store_string y2 qv2 )
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z2)
  **  (store_term z1 qterm1 )
.

Definition alpha_equiv_partial_solve_wit_13_pure := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z2: Z) (z1: Z) (y2: Z) (y1: Z) (qt2: quant_type) (qv2: (@list Z)) (qterm2: term) (qt1: quant_type) (qv1: (@list Z)) (qterm1: term) (retval_2: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (y1 <> 0) |] 
  &&  [| (y2 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval_2 = (list_Z_cmp (qv1) (qv2))) |] 
  &&  [| ((qtID (qt1)) = (qtID (qt2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (term1 = (TermQuant (qt1) (qv1) (qterm1))) |] 
  &&  [| (term2 = (TermQuant (qt2) (qv2) (qterm2))) |] 
  &&  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 1) |] 
  &&  [| ((termtypeID (term1)) <> 2) |] 
  &&  [| ((termtypeID (term1)) = 3) |]
  &&  (store_term z2 qterm2 )
  **  (store_term retval qterm2 )
  **  ((( &( "t21" ) )) # Ptr  |->_)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y1)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y2)
  **  (store_string y1 qv1 )
  **  (store_string y2 qv2 )
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z2)
  **  (store_term z1 qterm1 )
|--
  [| (y1 <> 0) |] 
  &&  [| (y2 <> 0) |] 
  &&  [| (retval <> 0) |]
.

Definition alpha_equiv_partial_solve_wit_13_aux := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z2: Z) (z1: Z) (y2: Z) (y1: Z) (qt2: quant_type) (qv2: (@list Z)) (qterm2: term) (qt1: quant_type) (qv1: (@list Z)) (qterm1: term) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (y1 <> 0) |] 
  &&  [| (y2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = (list_Z_cmp (qv1) (qv2))) |] 
  &&  [| ((qtID (qt1)) = (qtID (qt2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (term1 = (TermQuant (qt1) (qv1) (qterm1))) |] 
  &&  [| (term2 = (TermQuant (qt2) (qv2) (qterm2))) |] 
  &&  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 1) |] 
  &&  [| ((termtypeID (term1)) <> 2) |] 
  &&  [| ((termtypeID (term1)) = 3) |]
  &&  (store_term z2 qterm2 )
  **  (store_term retval_2 qterm2 )
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y2)
  **  (store_string y1 qv1 )
  **  (store_string y2 qv2 )
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z2)
  **  (store_term z1 qterm1 )
|--
  [| (y1 <> 0) |] 
  &&  [| (y2 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (y1 <> 0) |] 
  &&  [| (y2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = (list_Z_cmp (qv1) (qv2))) |] 
  &&  [| ((qtID (qt1)) = (qtID (qt2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (term1 = (TermQuant (qt1) (qv1) (qterm1))) |] 
  &&  [| (term2 = (TermQuant (qt2) (qv2) (qterm2))) |] 
  &&  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 1) |] 
  &&  [| ((termtypeID (term1)) <> 2) |] 
  &&  [| ((termtypeID (term1)) = 3) |]
  &&  (store_term retval_2 qterm2 )
  **  (store_string y2 qv2 )
  **  (store_string y1 qv1 )
  **  (store_term z2 qterm2 )
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z2)
  **  (store_term z1 qterm1 )
.

Definition alpha_equiv_partial_solve_wit_13 := alpha_equiv_partial_solve_wit_13_pure -> alpha_equiv_partial_solve_wit_13_aux.

Definition alpha_equiv_partial_solve_wit_14 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z2: Z) (z1: Z) (y2: Z) (y1: Z) (qt2: quant_type) (qv2: (@list Z)) (qterm2: term) (qt1: quant_type) (qv1: (@list Z)) (qterm1: term) (retval: Z) (retval_2: Z) (retval_3: Z) ,
  [| (retval_3 = retval_2) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (y1 <> 0) |] 
  &&  [| (y2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = (list_Z_cmp (qv1) (qv2))) |] 
  &&  [| ((qtID (qt1)) = (qtID (qt2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (term1 = (TermQuant (qt1) (qv1) (qterm1))) |] 
  &&  [| (term2 = (TermQuant (qt2) (qv2) (qterm2))) |] 
  &&  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 1) |] 
  &&  [| ((termtypeID (term1)) <> 2) |] 
  &&  [| ((termtypeID (term1)) = 3) |]
  &&  (store_term retval_2 (term_subst_v (qv1) (qv2) (qterm2)) )
  **  (store_string y1 qv1 )
  **  (store_string y2 qv2 )
  **  (store_term z2 qterm2 )
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z2)
  **  (store_term z1 qterm1 )
|--
  [| (retval_3 = retval_2) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (y1 <> 0) |] 
  &&  [| (y2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = (list_Z_cmp (qv1) (qv2))) |] 
  &&  [| ((qtID (qt1)) = (qtID (qt2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (term1 = (TermQuant (qt1) (qv1) (qterm1))) |] 
  &&  [| (term2 = (TermQuant (qt2) (qv2) (qterm2))) |] 
  &&  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 1) |] 
  &&  [| ((termtypeID (term1)) <> 2) |] 
  &&  [| ((termtypeID (term1)) = 3) |]
  &&  (store_term z1 qterm1 )
  **  (store_term retval_3 (term_subst_v (qv1) (qv2) (qterm2)) )
  **  (store_string y1 qv1 )
  **  (store_string y2 qv2 )
  **  (store_term z2 qterm2 )
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z2)
.

Definition alpha_equiv_partial_solve_wit_15 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z2: Z) (z1: Z) (y2: Z) (y1: Z) (qt2: quant_type) (qv2: (@list Z)) (qterm2: term) (qt1: quant_type) (qv1: (@list Z)) (qterm1: term) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (retval_4 = (term_alpha_eqn (qterm1) ((term_subst_v (qv1) (qv2) (qterm2))))) |] 
  &&  [| (retval_3 = retval_2) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (y1 <> 0) |] 
  &&  [| (y2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = (list_Z_cmp (qv1) (qv2))) |] 
  &&  [| ((qtID (qt1)) = (qtID (qt2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (term1 = (TermQuant (qt1) (qv1) (qterm1))) |] 
  &&  [| (term2 = (TermQuant (qt2) (qv2) (qterm2))) |] 
  &&  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 1) |] 
  &&  [| ((termtypeID (term1)) <> 2) |] 
  &&  [| ((termtypeID (term1)) = 3) |]
  &&  (store_term z1 qterm1 )
  **  (store_term retval_3 (term_subst_v (qv1) (qv2) (qterm2)) )
  **  (store_string y1 qv1 )
  **  (store_string y2 qv2 )
  **  (store_term z2 qterm2 )
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z2)
|--
  [| (retval_4 = (term_alpha_eqn (qterm1) ((term_subst_v (qv1) (qv2) (qterm2))))) |] 
  &&  [| (retval_3 = retval_2) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (y1 <> 0) |] 
  &&  [| (y2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = (list_Z_cmp (qv1) (qv2))) |] 
  &&  [| ((qtID (qt1)) = (qtID (qt2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (term1 = (TermQuant (qt1) (qv1) (qterm1))) |] 
  &&  [| (term2 = (TermQuant (qt2) (qv2) (qterm2))) |] 
  &&  [| ((termtypeID (term1)) = (termtypeID (term2))) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t2_pre <> 0) |] 
  &&  [| (t1_pre <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 0) |] 
  &&  [| ((termtypeID (term1)) <> 1) |] 
  &&  [| ((termtypeID (term1)) <> 2) |] 
  &&  [| ((termtypeID (term1)) = 3) |]
  &&  (store_term retval_3 (term_subst_v (qv1) (qv2) (qterm2)) )
  **  (store_term z1 qterm1 )
  **  (store_string y1 qv1 )
  **  (store_string y2 qv2 )
  **  (store_term z2 qterm2 )
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z2)
.

Definition alpha_equiv_which_implies_wit_1 := 
forall (term2: term) (term1: term) (t1: Z) (t2: Z) ,
  (store_term t1 term1 )
  **  (store_term t2 term2 )
|--
  [| (t1 <> 0) |] 
  &&  [| (t2 <> 0) |]
  &&  ((&((t1)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  (store_term' t1 term1 )
  **  (store_term' t2 term2 )
.

Definition alpha_equiv_which_implies_wit_2 := 
forall (term2: term) (term1: term) (t1: Z) (t2: Z) ,
  [| (t1 <> 0) |] 
  &&  [| (t2 <> 0) |] 
  &&  [| ((termtypeID (term1)) = 0) |] 
  &&  [| ((termtypeID (term1)) = (termtypeID (term2))) |]
  &&  ((&((t1)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  (store_term' t1 term1 )
  **  (store_term' t2 term2 )
|--
  EX (z: Z)  (y: Z)  (str2: (@list Z))  (str1: (@list Z)) ,
  [| (t1 <> 0) |] 
  &&  [| (t2 <> 0) |] 
  &&  [| (term1 = (TermVar (str1))) |] 
  &&  [| (term2 = (TermVar (str2))) |]
  &&  ((&((t1)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  ((&((t2)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> z)
  **  (store_string y str1 )
  **  (store_string z str2 )
.

Definition alpha_equiv_which_implies_wit_3 := 
forall (term2: term) (term1: term) (t1: Z) (t2: Z) ,
  [| (t1 <> 0) |] 
  &&  [| (t2 <> 0) |] 
  &&  [| ((termtypeID (term1)) = 1) |] 
  &&  [| ((termtypeID (term1)) = (termtypeID (term2))) |]
  &&  ((&((t1)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  (store_term' t1 term1 )
  **  (store_term' t2 term2 )
|--
  EX (typ2: const_type)  (con2: Z)  (typ1: const_type)  (con1: Z) ,
  [| (t1 <> 0) |] 
  &&  [| (t2 <> 0) |] 
  &&  [| (term1 = (TermConst (typ1) (con1))) |] 
  &&  [| (term2 = (TermConst (typ2) (con2))) |]
  &&  ((&((t1)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ1)))
  **  ((&((t2)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ2)))
  **  ((&((t1)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con1)
  **  ((&((t2)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con2)
.

Definition alpha_equiv_which_implies_wit_4 := 
forall (term2: term) (term1: term) (t1: Z) (t2: Z) ,
  [| (t1 <> 0) |] 
  &&  [| (t2 <> 0) |] 
  &&  [| ((termtypeID (term1)) = 2) |] 
  &&  [| ((termtypeID (term1)) = (termtypeID (term2))) |]
  &&  ((&((t1)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  (store_term' t1 term1 )
  **  (store_term' t2 term2 )
|--
  EX (z2: Z)  (z1: Z)  (y2: Z)  (y1: Z)  (lt2: term)  (rt2: term)  (lt1: term)  (rt1: term) ,
  [| (t1 <> 0) |] 
  &&  [| (t2 <> 0) |] 
  &&  [| (term1 = (TermApply (lt1) (rt1))) |] 
  &&  [| (term2 = (TermApply (lt2) (rt2))) |]
  &&  ((&((t1)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y1)
  **  ((&((t2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y2)
  **  ((&((t1)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z1)
  **  ((&((t2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z2)
  **  (store_term y1 lt1 )
  **  (store_term z1 rt1 )
  **  (store_term y2 lt2 )
  **  (store_term z2 rt2 )
.

Definition alpha_equiv_which_implies_wit_5 := 
forall (term2: term) (term1: term) (t1: Z) (t2: Z) ,
  [| (t1 <> 0) |] 
  &&  [| (t2 <> 0) |] 
  &&  [| ((termtypeID (term1)) = 3) |] 
  &&  [| ((termtypeID (term1)) = (termtypeID (term2))) |]
  &&  ((&((t1)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  (store_term' t1 term1 )
  **  (store_term' t2 term2 )
|--
  EX (z2: Z)  (z1: Z)  (y2: Z)  (y1: Z)  (qt2: quant_type)  (qv2: (@list Z))  (qterm2: term)  (qt1: quant_type)  (qv1: (@list Z))  (qterm1: term) ,
  [| (t1 <> 0) |] 
  &&  [| (t2 <> 0) |] 
  &&  [| (term1 = (TermQuant (qt1) (qv1) (qterm1))) |] 
  &&  [| (term2 = (TermQuant (qt2) (qv2) (qterm2))) |]
  &&  ((&((t1)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt1)))
  **  ((&((t2)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt2)))
  **  ((&((t1)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y1)
  **  ((&((t2)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y2)
  **  ((&((t1)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z1)
  **  ((&((t2)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z2)
  **  (store_string y1 qv1 )
  **  (store_term z1 qterm1 )
  **  (store_string y2 qv2 )
  **  (store_term z2 qterm2 )
.

Definition alpha_equiv_which_implies_wit_6 := 
forall (qv2: (@list Z)) (qv1: (@list Z)) (t1: Z) (v: Z) (t2: Z) (v_2: Z) ,
  ((&((t1)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> v)
  **  (store_string v qv1 )
  **  ((&((t2)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> v_2)
  **  (store_string v_2 qv2 )
|--
  [| (v <> 0) |] 
  &&  [| (v_2 <> 0) |]
  &&  ((&((t1)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> v)
  **  ((&((t2)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> v_2)
  **  (store_string v qv1 )
  **  (store_string v_2 qv2 )
.

Module Type VC_Correct.

Axiom proof_of_alpha_equiv_safety_wit_1 : alpha_equiv_safety_wit_1.
Axiom proof_of_alpha_equiv_safety_wit_2 : alpha_equiv_safety_wit_2.
Axiom proof_of_alpha_equiv_safety_wit_3 : alpha_equiv_safety_wit_3.
Axiom proof_of_alpha_equiv_safety_wit_4 : alpha_equiv_safety_wit_4.
Axiom proof_of_alpha_equiv_safety_wit_5 : alpha_equiv_safety_wit_5.
Axiom proof_of_alpha_equiv_safety_wit_6 : alpha_equiv_safety_wit_6.
Axiom proof_of_alpha_equiv_safety_wit_7 : alpha_equiv_safety_wit_7.
Axiom proof_of_alpha_equiv_safety_wit_8 : alpha_equiv_safety_wit_8.
Axiom proof_of_alpha_equiv_safety_wit_9 : alpha_equiv_safety_wit_9.
Axiom proof_of_alpha_equiv_safety_wit_10 : alpha_equiv_safety_wit_10.
Axiom proof_of_alpha_equiv_safety_wit_11 : alpha_equiv_safety_wit_11.
Axiom proof_of_alpha_equiv_safety_wit_12 : alpha_equiv_safety_wit_12.
Axiom proof_of_alpha_equiv_safety_wit_13 : alpha_equiv_safety_wit_13.
Axiom proof_of_alpha_equiv_safety_wit_14 : alpha_equiv_safety_wit_14.
Axiom proof_of_alpha_equiv_safety_wit_15 : alpha_equiv_safety_wit_15.
Axiom proof_of_alpha_equiv_entail_wit_1 : alpha_equiv_entail_wit_1.
Axiom proof_of_alpha_equiv_return_wit_1_1 : alpha_equiv_return_wit_1_1.
Axiom proof_of_alpha_equiv_return_wit_1_2 : alpha_equiv_return_wit_1_2.
Axiom proof_of_alpha_equiv_return_wit_2 : alpha_equiv_return_wit_2.
Axiom proof_of_alpha_equiv_return_wit_3_1 : alpha_equiv_return_wit_3_1.
Axiom proof_of_alpha_equiv_return_wit_3_2 : alpha_equiv_return_wit_3_2.
Axiom proof_of_alpha_equiv_return_wit_4 : alpha_equiv_return_wit_4.
Axiom proof_of_alpha_equiv_return_wit_5_1 : alpha_equiv_return_wit_5_1.
Axiom proof_of_alpha_equiv_return_wit_5_2 : alpha_equiv_return_wit_5_2.
Axiom proof_of_alpha_equiv_return_wit_5_3 : alpha_equiv_return_wit_5_3.
Axiom proof_of_alpha_equiv_return_wit_6 : alpha_equiv_return_wit_6.
Axiom proof_of_alpha_equiv_return_wit_7 : alpha_equiv_return_wit_7.
Axiom proof_of_alpha_equiv_return_wit_8 : alpha_equiv_return_wit_8.
Axiom proof_of_alpha_equiv_return_wit_9_1 : alpha_equiv_return_wit_9_1.
Axiom proof_of_alpha_equiv_return_wit_9_2 : alpha_equiv_return_wit_9_2.
Axiom proof_of_alpha_equiv_return_wit_10 : alpha_equiv_return_wit_10.
Axiom proof_of_alpha_equiv_partial_solve_wit_1 : alpha_equiv_partial_solve_wit_1.
Axiom proof_of_alpha_equiv_partial_solve_wit_2_pure : alpha_equiv_partial_solve_wit_2_pure.
Axiom proof_of_alpha_equiv_partial_solve_wit_2 : alpha_equiv_partial_solve_wit_2.
Axiom proof_of_alpha_equiv_partial_solve_wit_3 : alpha_equiv_partial_solve_wit_3.
Axiom proof_of_alpha_equiv_partial_solve_wit_4_pure : alpha_equiv_partial_solve_wit_4_pure.
Axiom proof_of_alpha_equiv_partial_solve_wit_4 : alpha_equiv_partial_solve_wit_4.
Axiom proof_of_alpha_equiv_partial_solve_wit_5_pure : alpha_equiv_partial_solve_wit_5_pure.
Axiom proof_of_alpha_equiv_partial_solve_wit_5 : alpha_equiv_partial_solve_wit_5.
Axiom proof_of_alpha_equiv_partial_solve_wit_6 : alpha_equiv_partial_solve_wit_6.
Axiom proof_of_alpha_equiv_partial_solve_wit_7 : alpha_equiv_partial_solve_wit_7.
Axiom proof_of_alpha_equiv_partial_solve_wit_8_pure : alpha_equiv_partial_solve_wit_8_pure.
Axiom proof_of_alpha_equiv_partial_solve_wit_8 : alpha_equiv_partial_solve_wit_8.
Axiom proof_of_alpha_equiv_partial_solve_wit_9 : alpha_equiv_partial_solve_wit_9.
Axiom proof_of_alpha_equiv_partial_solve_wit_10 : alpha_equiv_partial_solve_wit_10.
Axiom proof_of_alpha_equiv_partial_solve_wit_11 : alpha_equiv_partial_solve_wit_11.
Axiom proof_of_alpha_equiv_partial_solve_wit_12 : alpha_equiv_partial_solve_wit_12.
Axiom proof_of_alpha_equiv_partial_solve_wit_13_pure : alpha_equiv_partial_solve_wit_13_pure.
Axiom proof_of_alpha_equiv_partial_solve_wit_13 : alpha_equiv_partial_solve_wit_13.
Axiom proof_of_alpha_equiv_partial_solve_wit_14 : alpha_equiv_partial_solve_wit_14.
Axiom proof_of_alpha_equiv_partial_solve_wit_15 : alpha_equiv_partial_solve_wit_15.
Axiom proof_of_alpha_equiv_which_implies_wit_1 : alpha_equiv_which_implies_wit_1.
Axiom proof_of_alpha_equiv_which_implies_wit_2 : alpha_equiv_which_implies_wit_2.
Axiom proof_of_alpha_equiv_which_implies_wit_3 : alpha_equiv_which_implies_wit_3.
Axiom proof_of_alpha_equiv_which_implies_wit_4 : alpha_equiv_which_implies_wit_4.
Axiom proof_of_alpha_equiv_which_implies_wit_5 : alpha_equiv_which_implies_wit_5.
Axiom proof_of_alpha_equiv_which_implies_wit_6 : alpha_equiv_which_implies_wit_6.

End VC_Correct.
