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

Import naive_C_Rules.
Local Open Scope sac.

Inductive cnf_list_cell : Type :=
  | CNFCell (size: Z) (clause: list Z): cnf_list_cell.

Definition cnf_list : Type := list cnf_list_cell.

Inductive PreData : Type :=
  | PD (cnf_res: cnf_list) (prop_cnt: Z) (clause_cnt: Z): PreData.

(* Print store_int_array. *)

Module cnf_list_store_lists1.

Fixpoint sll_cnf_list (x: addr) (l: cnf_list): Assertion :=
  match l with
    | nil => [| x = NULL |] && emp
    | (CNFCell size clause) :: l0 => [| x <> NULL |] &&
                                   EX y z: addr,
                                    &(x # "cnf_list" ->ₛ "size") # Int |-> size **
                                    &(x # "cnf_list" ->ₛ "clause") # Ptr |-> y **
                                    &(x # "cnf_list" ->ₛ "next") # Ptr |-> z **
                                    store_int_array y size clause **
                                    sll_cnf_list z l0
  end.

End cnf_list_store_lists1.

Import cnf_list_store_lists1.

(* Definition zlength {A: Type} (l: list A) : Z :=
  Z.of_nat (List.length l). *)

Definition Z_union (l1 l2 : list Z) : list Z :=
  nodup Z.eq_dec (l1 ++ l2).


Fixpoint all_vars (l: cnf_list): list Z :=
  match l with
    | nil => nil
    | (CNFCell size clause) :: l0 => Z_union clause (all_vars l0)
  end.

Definition all_vars_cnt (l: cnf_list): Z :=
  Zlength (all_vars l).

(* Compute Z_union [1; 2; 3] [2; 4; 5; 1]. *)
  (* = [1; 2; 3; 4; 5] : list Z *)

Definition store_predata (x: addr) (p: PreData): Assertion :=
  match p with
    | PD cnf_res prop_cnt clause_cnt => [| x <> NULL |] && [| Zlength cnf_res = clause_cnt |] && [| all_vars_cnt cnf_res = prop_cnt |] &&
                                        EX y: addr,
                                         &(x # "PreData" ->ₛ "cnf_res") # Ptr |-> y **
                                         &(x # "PreData" ->ₛ "prop_cnt") # Int |-> prop_cnt **
                                         &(x # "PreData" ->ₛ "clause_cnt") # Int |-> clause_cnt **
                                         sll_cnf_list y cnf_res
  end.