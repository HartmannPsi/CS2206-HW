Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Permutation.
Require Import String.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Import ListNotations.
Local Open Scope list.
Require Import String.
Local Open Scope string.
From SimpleC.EE Require Import super_poly_sll2.

Import naive_C_Rules.
Local Open Scope sac.

Definition var_name : Type := list Z.

Module ast_enums1.

Inductive const_type : Type :=
  | CNum: const_type
  | CAdd: const_type
  | CMul: const_type
  | CEq: const_type
  | CLe: const_type
  | CAnd: const_type
  | COr: const_type
  | CImpl: const_type.

Inductive quant_type : Type :=
  | QForall: quant_type
  | QExists: quant_type.

Inductive term_type : Type :=
  | TVar: term_type
  | TConst: term_type
  | TApply: term_type
  | TQuant: term_type.

Inductive res_type : Type :=
  | BoolRes: res_type
  | TermList: res_type.

Definition valid_ct (t: const_type) := True.
  
Definition ctID (t: const_type) :=
  match t with
    | CNum => 0%Z
    | CAdd => 1%Z
    | CMul => 2%Z
    | CEq => 3%Z
    | CLe => 4%Z
    | CAnd => 5%Z
    | COr => 6%Z
    | CImpl => 7%Z
  end.
  
Definition valid_qt (t: quant_type) := True.
  
Definition qtID (t: quant_type) :=
  match t with
    | QForall => 0%Z
    | QExists => 1%Z
  end.

Definition valid_tt (t: term_type) := True.

Definition ttID (t: term_type) :=
  match t with
    | TVar => 0%Z
    | TConst => 1%Z
    | TApply => 2%Z
    | TQuant => 3%Z
  end.

Definition valid_rt (t: res_type) := True.

Definition rtID (t: res_type) :=
  match t with
    | BoolRes => 0%Z
    | TermList => 1%Z
  end.

End ast_enums1.

Module ast_enums2.

Definition const_type : Type := Z.
Definition quant_type : Type := Z.
Definition term_type : Type := Z.
Definition res_type : Type := Z.

Definition CNum : Z := 0%Z.
Definition CAdd : Z := 1%Z.
Definition CMul : Z := 2%Z.
Definition CEq : Z := 3%Z.
Definition CLe : Z := 4%Z.
Definition CAnd : Z := 5%Z.
Definition COr : Z := 6%Z.
Definition CImpl : Z := 7%Z.

Definition QForall : Z := 0%Z.
Definition QExists : Z := 1%Z.

Definition TVar : Z := 0%Z.
Definition TConst : Z := 1%Z.
Definition TApply : Z := 2%Z.
Definition TQuant : Z := 3%Z.

Definition BoolRes : Z := 0%Z.
Definition TermList : Z := 1%Z.

Definition valid_ct (t: const_type) :=
  0 <= t <= 7.

Definition ctID (t: const_type) := t.

Definition valid_qt (t: quant_type) :=
  0 <= t <= 1.

Definition qtID (t: quant_type) := t.

Definition valid_tt (t: quant_type) :=
  0 <= t <= 3.

Definition ttID (t: term_type) := t.

Definition valid_rt (t: res_type) :=
  0 <= t <= 1.

Definition rtID (t: res_type) := t.

End ast_enums2.

Import ast_enums1.

Module ast_term1.

Inductive term : Type :=
  | TermVar (ttype: term_type) (var: var_name): term
  | TermConst (ttype: term_type) (ctype: const_type) (content: Z): term
  | TermApply (ttype: term_type) (lt: term) (rt: term): term
  | TermQuant (ttype: term_type) (qtype: quant_type) (qvar: var_name) (body: term): term.

End ast_term1.

Module ast_term2.

Inductive sub_term : Type :=
  | TermVar (var: var_name): sub_term
  | TermConst (ctype: const_type) (content: Z): sub_term
  | TermApply (lt: term) (rt: term): sub_term
  | TermQuant (qtype: quant_type) (qvar: var_name) (body: term): sub_term

with term : Type :=
  Term (ttype: term_type) (body: sub_term): term.

End ast_term2.

Import ast_term1.

Definition term_list : Type := list term.

(* Definition var_sub : Type := var_name * term. *)

Inductive var_sub : Type :=
  | VarSub (name: var_name) (t: term): var_sub.

Definition var_sub_list : Type := list var_sub.

Module ast_solve_res1.

Inductive solve_res : Type :=
  | SRBool (rtype: res_type) (ans: Z): solve_res
  | SRTList (rtype: res_type) (l: term_list): solve_res.

End ast_solve_res1.

Module ast_solve_res2.

Inductive sub_solve_res : Type :=
  | SRBool (ans: bool): sub_solve_res
  | SRTList (l: term_list): sub_solve_res.

Definition solve_res : Type := res_type * sub_solve_res.

End ast_solve_res2.

Import ast_solve_res1.

(* 
Print store_array.
Print store_char. *)
(* Print store_char_array.
Print length. *)

(* Definition zlength {A: Type} (l: list A) : Z :=
  Z.of_nat (List.length l). *)

Fixpoint all_zero_list_nat (n: nat) : list Z :=
  match n with
    | O => nil
    | S n0 => 0 :: (all_zero_list_nat n0)
  end.

Definition all_zero_list (n: Z): list Z :=
  all_zero_list_nat (Z.to_nat n).

Definition store_string (x: addr) (str: var_name): Assertion :=
  EX n: Z,
  [| n >= 0 |] &&
  store_char_array x (Zlength (str ++ (all_zero_list n))) (str ++ (all_zero_list n)).

Fixpoint store_term (x: addr) (t: term): Assertion :=
  match t with
    | TermVar ttype var => [| ttype = TVar |] && [| x <> NULL |] &&
                           EX y: addr,
                            &(x # "term" ->ₛ "type") # Int |-> ttID TVar **
                            &(x # "term" ->ₛ "content" .ₛ "Var") # Ptr |-> y **
                            store_string y var
    | TermConst ttype ctype content => [| ttype = TConst |] && [| x <> NULL |] && [| valid_ct ctype |] &&
                                       &(x # "term" ->ₛ "type") # Int |-> ttID TConst **
                                       &(x # "term" ->ₛ "content" .ₛ "Const" .ₛ "type") # Int |-> ctID ctype **
                                       &(x # "term" ->ₛ "content" .ₛ "Const" .ₛ "content") # Int |-> content
    | TermApply ttype lt rt => [| ttype = TApply |] && [| x <> NULL |] &&
                               EX y z: addr,
                                &(x # "term" ->ₛ "type") # Int |-> ttID TApply **
                                &(x # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left") # Ptr |-> y **
                                &(x # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right") # Ptr |-> z **
                                store_term y lt ** store_term z rt
    | TermQuant ttype qtype qvar body => [| ttype = TQuant |] && [| x <> NULL |] && [| valid_qt qtype |] &&
                                         EX y z: addr,
                                          &(x # "term" ->ₛ "type") # Int |-> ttID TQuant **
                                          &(x # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type") # Int |-> qtID qtype **
                                          &(x # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var") # Ptr |-> y **
                                          &(x # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body") # Ptr |-> z **
                                          store_string y qvar ** store_term z body
  end.

Definition store_term_cell (x: addr) (t: term): Assertion :=
  [| x <> NULL |] &&
  EX y: addr,
    &(x # "term_list" ->ₛ "element") # Ptr |-> y **
    store_term y t.

(* Definition link_term_cell (x y: addr): Assertion :=
  [| x <> NULL |] &&
  &(x # "term_list" ->ₛ "next") # Ptr |-> y. *)

Definition store_var_sub (x: addr) (v: var_sub): Assertion :=
  match v with
    | VarSub name term => [| x <> NULL |] &&
                          EX y z: addr,
                           &(x # "var_sub" ->ₛ "var") # Ptr |-> y **
                           &(x # "var_sub" ->ₛ "sub_term") # Ptr |-> z **
                           store_string y name ** store_term z term
  end.

Definition store_var_sub_cell (x: addr) (v: var_sub): Assertion :=
  [| x <> NULL |] &&
  EX y: addr,
    &(x # "var_sub_list" ->ₛ "cur") # Ptr |-> y **
    store_var_sub y v.

(* Definition link_var_sub_cell (x y: addr): Assertion :=
  [| x <> NULL |] &&
  &(x # "var_sub_list" ->ₛ "next") # Ptr |-> y. *)

Module ast_store_lists1.

Fixpoint sll_term_list (x: addr) (l: term_list): Assertion :=
  match l with
    | nil => [| x = NULL |] && emp
    | a :: l0 => [| x <> NULL |] &&
                 EX y z: addr,
                  &(x # "term_list" ->ₛ "element") # Ptr |-> y **
                  &(x # "term_list" ->ₛ "next") # Ptr |-> z **
                  store_term y a ** sll_term_list z l0
  end.

Fixpoint sll_var_sub_list (x: addr) (l: var_sub_list): Assertion :=
  match l with
    | nil => [| x = NULL |] && emp
    | a :: l0 => [| x <> NULL |] &&
                 EX y z: addr,
                  &(x # "var_sub_list" ->ₛ "cur") # Ptr |-> y **
                  &(x # "var_sub_list" ->ₛ "next") # Ptr |-> z **
                  store_var_sub y a ** sll_var_sub_list z l0
  end.

End ast_store_lists1.

Module ast_store_lists2.

Definition sll_term_list (x: addr) (l: term_list): Assertion :=
  sll store_term_cell "term_list" "next" x l.

Definition sllseg_term_list (x: addr) (y: addr) (l: term_list): Assertion :=
  sllseg store_term_cell "term_list" "next" x y l.

Definition sllbseg_term_list (x: addr) (y: addr) (l: term_list): Assertion :=
  sllbseg store_term_cell "term_list" "next" x y l.

Definition sll_var_sub_list (x: addr) (l: var_sub_list): Assertion :=
  sll store_var_sub_cell "var_sub_list" "next" x l.

Definition sllseg_var_sub_list (x: addr) (y: addr) (l: var_sub_list): Assertion :=
  sllseg store_var_sub_cell "var_sub_list" "next" x y l.

Definition sllbseg_var_sub_list (x: addr) (y: addr) (l: var_sub_list): Assertion :=
  sllbseg store_var_sub_cell "var_sub_list" "next" x y l.

End ast_store_lists2.

Import ast_store_lists2.

Definition store_solve_res (x: addr) (s: solve_res): Assertion :=
  match s with
    | SRBool rtype ans => [| x <> NULL |] && [| rtype = BoolRes |] && [| 0 <= ans <= 1 |] &&
                          &(x # "solve_res" ->ₛ "type") # Int |-> rtID BoolRes **
                          &(x # "solve_res" ->ₛ "d" .ₛ "ans") # Char |-> ans
    | SRTList rtype l => [| x <> NULL |] && [| rtype = TermList |] &&
                         EX y: addr,
                          &(x # "solve_res" ->ₛ "type") # Int |-> rtID TermList **
                          &(x # "solve_res" ->ₛ "d" .ₛ "list") # Ptr |-> y **
                          sll_term_list y l
  end.

Inductive ImplyProp : Type :=
  | ImplP (assum: term) (concl: term): ImplyProp.

Definition store_ImplyProp (x: addr) (p: ImplyProp): Assertion :=
  match p with
    | ImplP assum concl => [| x <> NULL |] &&
                           EX y z: addr,
                            &(x # "ImplyProp" ->ₛ "assum") # Ptr |-> y **
                            &(x # "ImplyProp" ->ₛ "concl") # Ptr |-> z **
                            store_term y assum ** store_term z concl
  end.