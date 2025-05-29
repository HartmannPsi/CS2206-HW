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
From SimpleC.EE Require Import smt_lang_lib.

Definition cnf_list_cell := list Z.

Definition cnf_list : Type := list (list Z).

(* Inductive PreData : Type :=
  | PD (cnf_res: cnf_list) (prop_cnt: Z) (clause_cnt: Z): PreData. *)

(* Print store_int_array. *)
Definition init_int_array (x: addr) (size: Z): Assertion :=
  store_int_array x size (all_zero_list size).

Definition store_clause (x: addr) (clause: list Z): Assertion :=
 [| Zlength clause <= 3 |] && [| Forall (fun z => z <> 0) clause |] &&
  store_int_array x 3%Z (clause ++ all_zero_list (3 - Zlength clause)).

Definition store_cnf_list_cell (x: addr) (clause: list Z): Assertion :=
 [| x <> NULL |] && EX y: addr,
  &(x # "cnf_list" ->ₛ "size") # Int |-> 3%Z **
  &(x # "cnf_list" ->ₛ "clause") # Ptr |-> y **
  store_clause y clause.

Module cnf_list_store_lists.

Definition sll_cnf_list (x: addr) (l: cnf_list): Assertion :=
  sll store_cnf_list_cell "cnf_list" "next" x l.

Definition sllseg_cnf_list (x: addr) (y: addr) (l: cnf_list): Assertion :=
  sllseg store_cnf_list_cell "cnf_list" "next" x y l.

Definition sllbseg_cnf_list (x: addr) (y: addr) (l: cnf_list): Assertion :=
  sllbseg store_cnf_list_cell "cnf_list" "next" x y l.

End cnf_list_store_lists.

Import cnf_list_store_lists.

(* Definition Z_union (l1 l2 : list Z) : list Z :=
  nodup Z.eq_dec (l1 ++ l2).

Fixpoint all_vars (l: cnf_list): list Z :=
  match l with
    | nil => nil
    | (CNFCell size clause) :: l0 => Z_union clause (all_vars l0)
  end.

Definition all_vars_cnt (l: cnf_list): Z :=
  Zlength (all_vars l). *)

Fixpoint max_element (l: list Z): Z :=
  match l with
    | nil => 0%Z
    | h :: t => Z.max h (max_element t)
  end.

Fixpoint min_element (l: list Z): Z :=
  match l with
    | nil => 0%Z
    | h :: t => Z.min h (min_element t)
  end.
  
Fixpoint max_cnf (l: cnf_list): Z :=
  match l with
    | nil => 0%Z
    | clause :: t => Z.max (max_element clause) (max_cnf t)
  end.

Fixpoint min_cnf (l: cnf_list): Z :=
  match l with
    | nil => 0%Z
    | clause :: t => Z.min (min_element clause) (min_cnf t)
  end.

Definition prop_cnt_inf (l: cnf_list): Z :=
  Z.max (max_cnf l) (Z.abs (min_cnf l)).

Definition store_predata (x: addr) (cnf_res: cnf_list) (prop_cnt clause_cnt: Z): Assertion :=
 [| x <> NULL |] && [| Zlength cnf_res = clause_cnt |] &&
 [| prop_cnt_inf cnf_res <= prop_cnt |] &&
  EX y: addr,
    &(x # "PreData" ->ₛ "cnf_res") # Ptr |-> y **
    &(x # "PreData" ->ₛ "prop_cnt") # Int |-> prop_cnt **
    &(x # "PreData" ->ₛ "clause_cnt") # Int |-> clause_cnt **
    sll_cnf_list y cnf_res.

(* Definition  (l: list Z): cnf_list_cell :=
  CNFCell 3 l. *)

Notation "x <>? y" := (negb (Z.eqb x y)) (at level 70).
Notation "x ==? y" := (Z.eq_dec x y) (at level 70).

Import smt_lang_enums1.

(* p3 <-> (p1 op p2) to cnf *)
(* Definition iff2cnf_binary (p1 p2 p3: Z) (op: SmtPropBop): cnf_list :=
  match op with
    | SMTPROP_AND => let c1 := [p1; -p3] in
            let c2 := [p2; -p3] in
              let c3 := if (p1 ==? p2) then [-p1; p3] else [-p1; -p2; p3] in
                c1 :: c2 :: c3 :: nil
    | SMTPROP_OR => let c1 := [-p1; p3] in
            let c2 := [-p2; p3] in
              let c3 := if (p1 ==? p2) then [p1; -p3] else [p1; p2; -p3] in
                c1 :: c2 :: c3 :: nil
    | SMTPROP_IMPLY => if (p1 ==? p2) then
              ( (p3 :: nil)) :: nil
           else
            let c1 := [p1; p3] in
              let c2 := [-p2; p3] in
                let c3 := [-p1; p2; -p3] in
                  c1 :: c2 :: c3 :: nil

    | SMTPROP_IFF => if (p1 ==? p2) then
            ( (p3 :: nil)) :: nil
           else
            let c1 := [p1; p2; p3] in
              let c2 := [-p1; -p2; p3] in
                let c3 := [p1; -p2; -p3] in
                  let c4 := [-p1; p2; -p3] in
                    c1 :: c2 :: c3 :: c4 :: nil
  end.

Definition iff2cnf_length_binary (p1 p2 p3: Z) (op: SmtPropBop): Z :=
  match op with
    | SMTPROP_AND => 3%Z
    | SMTPROP_OR => 3%Z
    | SMTPROP_IMPLY => if (p1 ==? p2) then 1%Z else 3%Z
    | SMTPROP_IFF => if (p1 ==? p2) then 1%Z else 4%Z
  end. *)

Definition iff2cnf_binary (p1 p2 p3: Z) (op: Z): cnf_list :=
  match op with
    | 0 => let c1 := [p1; -p3] in
            let c2 := [p2; -p3] in
              let c3 := if (p1 ==? p2) then [-p1; p3] else [-p1; -p2; p3] in
                c1 :: c2 :: c3 :: nil
    | 1 => let c1 := [-p1; p3] in
            let c2 := [-p2; p3] in
              let c3 := if (p1 ==? p2) then [p1; -p3] else [p1; p2; -p3] in
                c1 :: c2 :: c3 :: nil
    | 2 => if (p1 ==? p2) then
              ( (p3 :: nil)) :: nil
            else
            let c1 := [p1; p3] in
              let c2 := [-p2; p3] in
                let c3 := [-p1; p2; -p3] in
                  c1 :: c2 :: c3 :: nil

    | 3 => if (p1 ==? p2) then
            ( (p3 :: nil)) :: nil
            else
            let c1 := [p1; p2; p3] in
              let c2 := [-p1; -p2; p3] in
                let c3 := [p1; -p2; -p3] in
                  let c4 := [-p1; p2; -p3] in
                    c1 :: c2 :: c3 :: c4 :: nil
    | _ => nil
  end.

Definition iff2cnf_length_binary (p1 p2 p3: Z) (op: Z): Z :=
  match op with
    | 0 => 3%Z
    | 1 => 3%Z
    | 2 => if (p1 ==? p2) then 1%Z else 3%Z
    | 3 => if (p1 ==? p2) then 1%Z else 4%Z
    | _ => 0%Z
  end.

Definition iff2cnf_unary (p2 p3: Z): cnf_list :=
  let c1 := [p2; p3] in
    let c2 := [-p2; -p3] in
      c1 :: c2 :: nil.

  (* 0 => AND
     1 => OR
     2 => IMPLY
     3 => IFF
     4 => NOT *)