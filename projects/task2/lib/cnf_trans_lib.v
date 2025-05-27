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

From SimpleC.EE Require Import super_poly_sll2.
From SimpleC.EE Require Import malloc.

Inductive cnf_list_cell : Type :=
  | CNFCell (size: Z) (clause: list Z): cnf_list_cell.

Definition cnf_list : Type := list cnf_list_cell.

(* Inductive PreData : Type :=
  | PD (cnf_res: cnf_list) (prop_cnt: Z) (clause_cnt: Z): PreData. *)

(* Print store_int_array. *)
Definition init_int_array (x: addr) (size: Z): Assertion :=
  store_int_array x size (all_zero_list size).

Definition store_clause (x: addr) (clause: list Z): Assertion :=
  [| Zlength clause <= 3 |] && [| Forall (fun z => z <> 0) clause |] &&
  store_int_array x 3%Z (clause ++ all_zero_list (3 - Zlength clause)).

Definition store_cnf_list_cell (x: addr) (c: cnf_list_cell): Assertion :=
  match c with
    | CNFCell size clause => [| x <> NULL |] && [| Zlength clause = size |] &&
                             EX y: addr,
                              &(x # "cnf_list" ->ₛ "size") # Int |-> size **
                              &(x # "cnf_list" ->ₛ "clause") # Ptr |-> y **
                              store_clause y clause
  end.

(* Definition link_cnf_list_cell (x y: addr): Assertion :=
  [| x <> NULL |] &&
  &(x # "cnf_list" ->ₛ "next") # Ptr |-> y. *)

Module cnf_list_store_lists.

Definition sll_cnf_list (x: addr) (l: cnf_list): Assertion :=
  sll store_cnf_list_cell "cnf_list" "next" x l.

Definition sllseg_cnf_list (x: addr) (y: addr) (l: cnf_list): Assertion :=
  sllseg store_cnf_list_cell "cnf_list" "next" x y l.

Definition sllbseg_cnf_list (x: addr) (y: addr) (l: cnf_list): Assertion :=
  sllbseg store_cnf_list_cell "cnf_list" "next" x y l.

End cnf_list_store_lists.

Import cnf_list_store_lists.

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

Definition store_predata (x: addr) (cnf_res: cnf_list) (prop_cnt clause_cnt: Z): Assertion :=
  [| x <> NULL |] && [| Zlength cnf_res = clause_cnt |] &&
  [| all_vars_cnt cnf_res = prop_cnt |] &&
  EX y: addr,
    &(x # "PreData" ->ₛ "cnf_res") # Ptr |-> y **
    &(x # "PreData" ->ₛ "prop_cnt") # Int |-> prop_cnt **
    &(x # "PreData" ->ₛ "clause_cnt") # Int |-> clause_cnt **
    sll_cnf_list y cnf_res.

Definition cons_cnf_cell (l: list Z): cnf_list_cell :=
  CNFCell 3 l.

Notation "x <>? y" := (negb (Z.eqb x y)) (at level 70).
Notation "x ==? y" := (Z.eq_dec x y) (at level 70).

(* p3 <-> (p1 op p2) to cnf *)
Definition iff2cnf (p1 p2 p3: Z) (op: Z): cnf_list :=
  match op with
    | 0 => let c1 := cons_cnf_cell [p1; -p3] in
            let c2 := cons_cnf_cell [p2; -p3] in
              let c3 := if (p1 ==? p2) then cons_cnf_cell [-p1; p3] else cons_cnf_cell [-p1; -p2; p3] in
                c1 :: c2 :: c3 :: nil
    | 1 => let c1 := cons_cnf_cell [-p1; p3] in
            let c2 := cons_cnf_cell [-p2; p3] in
              let c3 := if (p1 ==? p2) then cons_cnf_cell [p1; -p3] else cons_cnf_cell [p1; p2; -p3] in
                c1 :: c2 :: c3 :: nil
    | 2 => if (p1 ==? p2) then
              (cons_cnf_cell (p3 :: nil)) :: nil
           else
            let c1 := cons_cnf_cell [p1; p3] in
              let c2 := cons_cnf_cell [-p2; p3] in
                let c3 := cons_cnf_cell [-p1; p2; -p3] in
                  c1 :: c2 :: c3 :: nil

    | 3 => if (p1 ==? p2) then
            (cons_cnf_cell (p3 :: nil)) :: nil
           else
            let c1 := cons_cnf_cell [p1; p2; p3] in
              let c2 := cons_cnf_cell [-p1; -p2; p3] in
                let c3 := cons_cnf_cell [p1; -p2; -p3] in
                  let c4 := cons_cnf_cell [-p1; p2; -p3] in
                    c1 :: c2 :: c3 :: c4 :: nil

    | 4 => let c1 := cons_cnf_cell [p2; p3] in
            let c2 := cons_cnf_cell [-p2; -p3] in
              c1 :: c2 :: nil
    | _ => nil
  end.

Definition iff2cnf_length (p1 p2 p3: Z) (op: Z): Z :=
  match op with
    | 0 => 3%Z
    | 1 => 3%Z
    | 2 => if (p1 ==? p2) then 1%Z else 3%Z
    | 3 => if (p1 ==? p2) then 1%Z else 4%Z
    | 4 => 2%Z
    | _ => 0%Z
  end.
  (* 0 => AND
     1 => OR
     2 => IMPLY
     3 => IFF
     4 => NOT *)