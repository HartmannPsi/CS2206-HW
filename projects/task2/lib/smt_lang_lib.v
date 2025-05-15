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

From SimpleC.EE Require Import super_poly_sll.

Module smt_lang_enums1.

Inductive SmtPropBop : Type :=
  | SMTPROP_AND: SmtPropBop
  | SMTPROP_OR: SmtPropBop
  | SMTPROP_IMPLY: SmtPropBop
  | SMTPROP_IFF: SmtPropBop.

Inductive SmtPropUop : Type :=
  | SMTPROP_NOT: SmtPropUop.

Inductive SmtPropType : Type :=
  | SMTB_PROP: SmtPropType
  | SMTU_PROP: SmtPropType
  | SMT_PROPVAR: SmtPropType.

Definition SmtPBID (t: SmtPropBop) : Z :=
  match t with
    | SMTPROP_AND => 0%Z
    | SMTPROP_OR => 1%Z
    | SMTPROP_IMPLY => 2%Z
    | SMTPROP_IFF => 3%Z
  end.

Definition SmtPUID (t: SmtPropUop) : Z :=
  match t with
    | SMTPROP_NOT => 4%Z
  end.

Definition SmtPTID (t: SmtPropType) : Z :=
  match t with
    | SMTB_PROP => 5%Z
    | SMTU_PROP => 6%Z
    | SMT_PROPVAR => 7%Z
  end.

Definition valid_SmtPB (t: SmtPropBop) := True.
Definition valid_SmtPU (t: SmtPropUop) := True.
Definition valid_SmtPT (t: SmtPropType) := True.

End smt_lang_enums1.

Import smt_lang_enums1.

Inductive SmtProp : Type :=
  | SmtB (type: SmtPropType) (op: SmtPropBop) (lt: SmtProp) (rt: SmtProp): SmtProp
  | SmtU (type: SmtPropType) (op: SmtPropUop) (prop: SmtProp): SmtProp
  | SmtV (type: SmtPropType) (var: Z): SmtProp.

Definition SmtProplist : Type := list SmtProp.

Fixpoint store_SmtProp (x: addr) (s: SmtProp) : Assertion :=
  match s with
    | SmtB type op lt rt => [| x <> NULL |] && [| type = SMTB_PROP |] && [| valid_SmtPB op |] &&
                            EX y z: addr,
                             &(x # "SmtProp" ->ₛ "type") # Int |-> SmtPTID SMTB_PROP **
                             &(x # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "op") # Int |-> SmtPBID op **
                             &(x # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop1") # Ptr |-> y **
                             &(x # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop2") # Ptr |-> z **
                             store_SmtProp y lt **
                             store_SmtProp z rt
    | SmtU type op prop => [| x <> NULL |] && [| type = SMTU_PROP |] && [| valid_SmtPU op |] &&
                           EX y: addr,
                            &(x # "SmtProp" ->ₛ "type") # Int |-> SmtPTID SMTU_PROP **
                            &(x # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "op") # Int |-> SmtPUID op **
                            &(x # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "prop1") # Ptr |-> y **
                            store_SmtProp y prop
    | SmtV type var => [| x <> NULL |] && [| type = SMT_PROPVAR |] &&
                       &(x # "SmtProp" ->ₛ "type") # Int |-> SmtPTID SMT_PROPVAR **
                       &(x # "SmtProp" ->ₛ "prop" .ₛ "Propvar") # Int |-> var
  end.

Module smt_lang_store_lists1.

Fixpoint sll_SmtProplist (x: addr) (l: SmtProplist): Assertion :=
  match l with
    | nil => [| x = NULL |] && emp
    | s :: l0 => [| x <> NULL |] &&
                EX y z: addr,
                 &(x # "SmtProplist" ->ₛ "prop") # Ptr |-> y **
                 &(x # "SmtProplist" ->ₛ "next") # Ptr |-> z **
                 store_SmtProp z s **
                 sll_SmtProplist y l0
  end.

End smt_lang_store_lists1.

Module smt_lang_store_lists2.

Definition sll_SmtProplist (x: addr) (l: SmtProplist): Assertion :=
  sll store_SmtProp x l "SmtProplist" "prop" "next".

Definition sllseg_SmtProplist (x: addr) (y: addr) (l: SmtProplist): Assertion :=
  sllseg store_SmtProp x y l "SmtProplist" "prop" "next".

Definition sllbseg_SmtProplist (x: addr) (y: addr) (l: SmtProplist): Assertion :=
  sllbseg store_SmtProp x y l "SmtProplist" "prop" "next".
  
End smt_lang_store_lists2.

Import smt_lang_store_lists2.