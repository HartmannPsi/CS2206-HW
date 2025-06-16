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
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Program.Wf.
Local Open Scope string.
From SimpleC.EE Require Import super_poly_sll2.
From SimpleC.EE Require Import malloc.

Import naive_C_Rules.
Local Open Scope sac.

Definition var_name : Type := list Z.

(* all about ast basic structure *)

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
  
Definition qtID (t: quant_type) :=
  match t with
    | QForall => 0%Z
    | QExists => 1%Z
  end.

Definition ttID (t: term_type) :=
  match t with
    | TVar => 0%Z
    | TConst => 1%Z
    | TApply => 2%Z
    | TQuant => 3%Z
  end.

Inductive term : Type :=
  | TermVar (var: var_name): term
  | TermConst (ctype: const_type) (content: Z): term
  | TermApply (lt: term) (rt: term): term
  | TermQuant (qtype: quant_type) (qvar: var_name) (body: term): term.

Definition term_list : Type := list term.

Definition termtypeID (t: term) : Z :=
  match t with
    | TermVar _ => 0%Z
    | TermConst _ _ => 1%Z
    | TermApply _ _ => 2%Z
    | TermQuant _ _ _ => 3%Z
  end.

(* Definition zlength {A: Type} (l: list A) : Z :=
  Z.of_nat (List.length l). *)

Definition store_string (x: addr) (str: var_name): Assertion :=
  EX n: Z,
  [| x <> NULL |] &&
  [| n >= 0 |] &&
  store_char_array x (Zlength (str ++ (all_zero_list n))) (str ++ (all_zero_list n)).

Fixpoint store_term (x: addr) (t: term): Assertion :=
  [| x <> NULL |] && &(x # "term" ->ₛ "type") # Int |-> termtypeID t **
  match t with
    | TermVar var => EX y: addr,
                    &(x # "term" ->ₛ "content" .ₛ "Var") # Ptr |-> y **
                    store_string y var
    | TermConst ctype content => &(x # "term" ->ₛ "content" .ₛ "Const" .ₛ "type") # Int |-> ctID ctype **
                                &(x # "term" ->ₛ "content" .ₛ "Const" .ₛ "content") # Int |-> content
    | TermApply lt rt => EX y z: addr,
                        &(x # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left") # Ptr |-> y **
                        &(x # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right") # Ptr |-> z **
                        store_term y lt ** store_term z rt
    | TermQuant qtype qvar body => EX y z: addr,
                                  &(x # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type") # Int |-> qtID qtype **
                                  &(x # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var") # Ptr |-> y **
                                  &(x # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body") # Ptr |-> z **
                                  store_string y qvar ** store_term z body
  end.

Definition store_term' (x: addr) (t: term): Assertion :=
  match t with
    | TermVar var => EX y: addr,
                      &(x # "term" ->ₛ "content" .ₛ "Var") # Ptr |-> y **
                      store_string y var
    | TermConst ctype content => &(x # "term" ->ₛ "content" .ₛ "Const" .ₛ "type") # Int |-> ctID ctype **
                                 &(x # "term" ->ₛ "content" .ₛ "Const" .ₛ "content") # Int |-> content
    | TermApply lt rt => EX y z: addr,
                          &(x # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left") # Ptr |-> y **
                          &(x # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right") # Ptr |-> z **
                          store_term y lt ** store_term z rt
    | TermQuant qtype qvar body => EX y z: addr,
                                    &(x # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type") # Int |-> qtID qtype **
                                    &(x # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var") # Ptr |-> y **
                                    &(x # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body") # Ptr |-> z **
                                    store_string y qvar ** store_term z body
  end.

Lemma store_term_unfold: forall x t,
  store_term x t |--
  [| x <> NULL |] &&
  &(x # "term" ->ₛ "type") # Int |-> termtypeID t **
  store_term' x t.
Proof.
  intros.
  unfold store_term, store_term'.
  destruct t; fold store_term; entailer!.
Qed.

Lemma store_term_fold: forall x t,
  [| x <> NULL |] &&
  &(x # "term" ->ₛ "type") # Int |-> termtypeID t **
  store_term' x t |--
  store_term x t.
Proof.
  intros.
  unfold store_term, store_term'.
  destruct t; fold store_term; entailer!.
Qed.

Lemma store_null: forall t q,
  store_term 0 t |-- q.
Proof.
  intros.
  pose proof (store_term_unfold 0 t).
  unfold NULL.
  sep_apply H.
  entailer!.
Qed.

Lemma store_null_left: forall t p q,
  store_term 0 t ** p |-- q.
Proof.
  intros.
  pose proof (store_term_unfold 0 t).
  unfold NULL.
  sep_apply H.
  entailer!.
Qed.

Lemma store_null_right: forall t p q,
  p ** store_term 0 t |-- q.
Proof.
  intros.
  pose proof (store_term_unfold 0 t).
  unfold NULL.
  sep_apply H.
  entailer!.
Qed.

Lemma store_term_fold_out: forall x t,
  x <> 0 ->
  &(x # "term" ->ₛ "type") # Int |-> termtypeID t **
  store_term' x t |--
  store_term x t.
Proof.
  intros.
  unfold store_term, store_term', NULL.
  destruct t; fold store_term.
  Intros y.
  Exists y.
  entailer!.
  entailer!.
  entailer!.
  Intros y z.
  Exists y z.
  entailer!.
  Intros y z.
  Exists y z.
  entailer!.
Qed.

Lemma store_term'_Var: forall x t,
  termtypeID t = 0%Z ->
  x <> NULL ->
  store_term' x t |--
  EX var, [| t = TermVar var |] && [| x <> NULL |] &&
  EX y: addr,
    &(x # "term" ->ₛ "content" .ₛ "Var") # Ptr |-> y **
    store_string y var.
Proof.
  intros.
  unfold store_term'.
  induction t; try discriminate.
  Intros y.
  Exists var y.
  entailer!.
Qed.

Lemma store_term'_Const: forall x t,
  termtypeID t = 1%Z ->
  x <> NULL ->
  store_term' x t |--
  EX ctype content, [| t = TermConst ctype content |] && [| x <> NULL |] &&
  &(x # "term" ->ₛ "content" .ₛ "Const" .ₛ "type") # Int |-> ctID ctype **
  &(x # "term" ->ₛ "content" .ₛ "Const" .ₛ "content") # Int |-> content.
Proof.
  intros.
  unfold store_term'.
  induction t; try discriminate.
  Intros.
  Exists ctype content.
  entailer!.
Qed.

Lemma store_term'_Apply: forall x t,
  termtypeID t = 2%Z ->
  x <> NULL ->
  store_term' x t |--
  EX lt rt, [| t = TermApply lt rt |] && [| x <> NULL |] &&
  EX y z: addr,
    &(x # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left") # Ptr |-> y **
    &(x # "term" ->ₛ "content" .ₛ "Apply" .ₛ  "right") # Ptr |-> z **
    store_term y lt ** store_term z rt.
Proof.
  intros.
  unfold store_term'.
  induction t; try discriminate.
  Intros y z.
  Exists t1 t2 y z.
  entailer!.
Qed.

Lemma store_term'_Quant: forall x t,
  termtypeID t = 3%Z ->
  x <> NULL ->
  store_term' x t |--
  EX qtype qvar body, [| t = TermQuant qtype qvar body |] && [| x <> NULL |] &&
  EX y z: addr,
    &(x # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type") # Int |-> qtID qtype **
    &(x # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var") # Ptr |-> y **
    &(x # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body") # Ptr |-> z **
    store_string y qvar ** store_term z body.
Proof.
  intros.
  unfold store_term'.
  induction t; try discriminate.
  Intros y z.
  Exists qtype qvar t y z.
  entailer!.
Qed.

Definition store_term_cell (x: addr) (t: term): Assertion :=
  [| x <> NULL |] &&
  EX y: addr,
    &(x # "term_list" ->ₛ "element") # Ptr |-> y **
    store_term y t.

Definition sll_term_list (x: addr) (l: term_list): Assertion :=
  sll store_term_cell "term_list" "next" x l.

Definition sllseg_term_list (x: addr) (y: addr) (l: term_list): Assertion :=
  sllseg store_term_cell "term_list" "next" x y l.

Definition sllbseg_term_list (x: addr) (y: addr) (l: term_list): Assertion :=
  sllbseg store_term_cell "term_list" "next" x y l.
    

(* all about ast var_sub *)

Inductive var_sub : Type :=
  | VarSub (name: var_name) (t: term): var_sub.

Definition var_sub_list : Type := list var_sub.


(* Definition var_sub_list : Type := list var_sub. *)
(* v is stored on addr x *)
Definition store_var_sub (x: addr) (v: var_sub): Assertion :=
  match v with
    | VarSub name term => [| x <> NULL |] &&
                          EX y z: addr,
                           &(x # "var_sub" ->ₛ "var") # Ptr |-> y **
                           &(x # "var_sub" ->ₛ "sub_term") # Ptr |-> z **
                           store_string y name ** store_term z term
  end.

(* the linked list node stores the var_sub type addr *)
Definition store_var_sub_cell (x: addr) (v: var_sub): Assertion :=
  [| x <> NULL |] &&
  EX y: addr, 
    &(x # "var_sub_list" ->ₛ "cur") # Ptr |-> y **
    store_var_sub y v.

Definition sll_var_sub_list (x: addr) (l: var_sub_list): Assertion :=
  sll store_var_sub_cell "var_sub_list" "next" x l.

Definition sllseg_var_sub_list (x: addr) (y: addr) (l: var_sub_list): Assertion :=
  sllseg store_var_sub_cell "var_sub_list" "next" x y l.

Definition sllbseg_var_sub_list (x: addr) (y: addr) (l: var_sub_list): Assertion :=
  sllbseg store_var_sub_cell "var_sub_list" "next" x y l.


(* all about ast solve result *)

Inductive res_type : Type :=
  | BoolRes: res_type
  | TermList: res_type.

Inductive solve_res : Type :=
  | SRBool (ans: Z): solve_res
  | SRTList (l: term_list): solve_res.


Definition restypeID (sr : solve_res) : Z :=
  match sr with
    | SRBool _ => 0%Z
    | SRTList _ => 1%Z
  end.

Definition store_solve_res (x: addr) (sr: solve_res): Assertion :=
  [| x <> NULL |] && &(x # "solve_res" ->ₛ "type") # Int |-> restypeID sr **
  match sr with
    | SRBool ans => &(x # "solve_res" ->ₛ "content" .ₛ "Bool") # Int |-> ans
    | SRTList l => EX y: addr,
                   &(x # "solve_res" ->ₛ "content" .ₛ "TermList") # Ptr |-> y **
                   sll_term_list y l
  end.

Definition store_solve_res' (x: addr) (sr: solve_res): Assertion :=
  match sr with
    | SRBool ans => [| x <> NULL |] && &(x # "solve_res" ->ₛ "content" .ₛ "Bool") # Int |-> ans
    | SRTList l => [| x <> NULL |] && EX y: addr,
                   &(x # "solve_res" ->ₛ "content" .ₛ "TermList") # Ptr |-> y **
                   sll_term_list y l
  end.

Lemma store_solve_res_unfold: forall x sr,
  store_solve_res x sr |--
  &(x # "solve_res" ->ₛ "type") # Int |-> restypeID sr **
  store_solve_res' x sr.
Proof.
  intros.
  unfold store_solve_res, store_solve_res'.
  destruct sr; fold store_solve_res; entailer!.
Qed.

Lemma store_solve_res_fold: forall x sr,
  &(x # "solve_res" ->ₛ "type") # Int |-> restypeID sr **
  store_solve_res' x sr |--
  store_solve_res x sr.
Proof.
  intros.
  unfold store_solve_res, store_solve_res'.
  destruct sr; fold store_solve_res; entailer!.
Qed.

Lemma store_solve_res'_Bool: forall x sr,
  restypeID sr = 0%Z ->
  store_solve_res' x sr |--
  EX ans, [| sr = SRBool ans |] && [| x <> NULL |] &&
  &(x # "solve_res" ->ₛ "content" .ₛ "Bool") # Int |-> ans.
Proof.
  intros.
  unfold store_solve_res'.
  induction sr; try discriminate.
  Intros.
  Exists ans.
  entailer!.
Qed.

Lemma store_solve_res'_List: forall x sr,
  restypeID sr = 1%Z ->
  store_solve_res' x sr |--
  EX l, [| sr = SRTList l |] && [| x <> NULL |] &&
  EX y: addr,
    &(x # "solve_res" ->ₛ "content" .ₛ "TermList") # Ptr |-> y **
    sll_term_list y l.
Proof.
  intros.
  unfold store_solve_res'.
  induction sr; try discriminate.
  Intros y.
  Exists l y.
  entailer!.
Qed.

(* all about ImplyProp *)

Inductive ImplyProp : Type :=
  | ImplP (assum: term) (concl: term): ImplyProp.

Definition store_ImplyProp (x y z: addr) (assum concl: term): Assertion :=
  [| x <> NULL |] &&
  &(x # "ImplyProp" ->ₛ "assum") # Ptr |-> y **
  &(x # "ImplyProp" ->ₛ "concl") # Ptr |-> z **
  store_term y assum ** store_term z concl.


Fixpoint list_Z_eqb (l1 l2 : list Z) : bool :=
  match l1, l2 with
  | [], [] => true
  | x1 :: t1, x2 :: t2 => Z.eqb x1 x2 && list_Z_eqb t1 t2
  | _, _ => false
  end.

Definition list_Z_cmp (l1 l2 : list Z) : Z :=
  if list_Z_eqb l1 l2 then 0 else 1.

Fixpoint term_subst_v (den src: var_name) (t: term): term :=
  match t with
    | TermVar v => if list_Z_eqb v src then TermVar den else TermVar v
    | TermConst ctype content => TermConst ctype content
    | TermApply lt rt => TermApply (term_subst_v den src lt) (term_subst_v den src rt)
    | TermQuant qtype qvar body =>
      if list_Z_eqb qvar src then
        TermQuant qtype qvar body
      else
        TermQuant qtype qvar (term_subst_v den src body)
  end.

Fixpoint term_subst_t (den: term) (src: var_name) (t: term): term :=
  match t with
    | TermVar v => if list_Z_eqb v src then den else TermVar v
    | TermConst ctype content => TermConst ctype content
    | TermApply lt rt => TermApply (term_subst_t den src lt) (term_subst_t den src rt)
    | TermQuant qtype qvar body =>
      if list_Z_eqb qvar src then
        TermQuant qtype qvar body
      else
        TermQuant qtype qvar (term_subst_t den src body)
  end.

Lemma list_Z_eqb_eq : forall l1 l2 : list Z,
  list_Z_eqb l1 l2 = true <-> l1 = l2.
Proof. 
  induction l1.
  + intros.
    destruct l2; [ split; try reflexivity | split; try discriminate ].
  + intros.
    destruct l2; [ split; try discriminate | split ].
    - unfold list_Z_eqb.
      fold list_Z_eqb.
      rewrite andb_true_iff.
      intros.
      destruct H as [Ha Hl].
      rewrite Z.eqb_eq in Ha.
      pose proof IHl1 l2.
      destruct H.
      pose proof H Hl.
      rewrite Ha, H1.
      reflexivity.
    - intros.
      injection H.
      intros.
      unfold list_Z_eqb.
      fold list_Z_eqb.
      rewrite andb_true_iff.
      pose proof IHl1 l2.
      destruct H2.
      pose proof H3 H0.
      split; [ | auto].
      rewrite Z.eqb_eq.
      auto.
Qed.

Lemma list_Z_eqb2eq : forall l1 l2 : list Z,
  list_Z_eqb l1 l2 = true -> l1 = l2.
Proof.
  apply list_Z_eqb_eq.
Qed. 

Lemma list_Z_eq2eqb : forall l1 l2 : list Z,
  l1 = l2 -> list_Z_eqb l1 l2 = true.
Proof.
  apply list_Z_eqb_eq.
Qed. 

Lemma list_Z_neqb_neq : forall l1 l2 : list Z,
  list_Z_eqb l1 l2 = false <-> l1 <> l2.
Proof.
  intros l1 l2. split.
  + intros H Hcontra.
    pose proof list_Z_eq2eqb l1 l2 Hcontra; congruence.
  + intros H.
    destruct (list_Z_eqb l1 l2) eqn:E.
    - pose proof list_Z_eqb2eq l1 l2 E; congruence.
    - reflexivity.  
Qed.

Lemma list_Z_neqb2neq : forall l1 l2 : list Z,
  list_Z_eqb l1 l2 = false -> l1 <> l2.
Proof.
  apply list_Z_neqb_neq.
Qed. 

Lemma list_Z_neq2neqb : forall l1 l2 : list Z,
  l1 <> l2 -> list_Z_eqb l1 l2 = false.
Proof.
  apply list_Z_neqb_neq.
Qed. 

Lemma list_Z_eqb_refl : forall (l : list Z),
  list_Z_eqb l l = true.
Proof.
  intros.
  apply list_Z_eqb_eq.
  reflexivity.
Qed.

Lemma list_Z_eqb_symm : forall (l1 l2 : list Z),
  list_Z_eqb l1 l2 = list_Z_eqb l2 l1.
Proof.
  intros.
  destruct (list_Z_eqb l1 l2) eqn:E.
  + pose proof list_Z_eqb2eq l1 l2 E.
    rewrite H; pose proof list_Z_eqb_refl l2; rewrite H0; auto.
  + pose proof list_Z_neqb2neq l1 l2 E.
    destruct (list_Z_eqb l2 l1) eqn:Heq.
    - pose proof list_Z_eqb2eq l2 l1 Heq; congruence.
    - auto.
Qed.

Lemma list_Z_eqb_trans : forall (l1 l2 l3 : list Z),
  list_Z_eqb l1 l2 = true ->
  list_Z_eqb l2 l3 = true ->
  list_Z_eqb l1 l3 = true.
Proof.
  intros.
  apply list_Z_eqb_eq.
  pose proof list_Z_eqb2eq l1 l2 H.
  pose proof list_Z_eqb2eq l2 l3 H0.
  rewrite H1, H2.
  reflexivity.
Qed.

(* alpha_equiv begin *)

Fixpoint term_not_free_var (t : term) (var : var_name) : Prop :=
  match t with
  | TermVar v => v <> var
  | TermConst _ _ => True
  | TermApply lt rt => term_not_free_var lt var /\ term_not_free_var rt var
  | TermQuant _ qvar body => qvar = var \/ qvar <> var /\ term_not_free_var body var
  end.

Fixpoint term_not_contain_var (t : term) (var : var_name) : Prop :=
  match t with
  | TermVar v => v <> var
  | TermConst _ _ => True
  | TermApply lt rt => term_not_contain_var lt var /\ term_not_contain_var rt var
  | TermQuant _ qvar body => qvar <> var /\ term_not_contain_var body var
  end.

Lemma not_contain_imply_not_free : forall (t : term) (var : var_name),
  term_not_contain_var t var -> term_not_free_var t var.
Proof.
  induction t; try intros; try unfold term_not_free_var; try unfold term_not_contain_var in H.
  + auto.
  + auto.
  + fold term_not_free_var; fold term_not_contain_var in H.
    destruct H as [Ha Hb].
    pose proof IHt1 var Ha.
    pose proof IHt2 var Hb.
    auto.
  + right; fold term_not_free_var; fold term_not_contain_var in H.
    destruct H as [Ha Hb].
    pose proof IHt var Hb.
    auto.
Qed. 

Fixpoint sub_thm (thm: term) (l: var_sub_list): term :=
  match l with 
    | nil => thm
    | (VarSub v t) :: l0 => 
      match thm with
        | TermQuant qtype qvar body =>
            sub_thm (term_subst_t t v body) l0
        | _ => thm
      end
  end.

(* Inductive term_alpha_eq : term -> term -> Prop :=
  | AlphaVar : forall v1 v2,
      v1 = v2 ->
      term_alpha_eq (TermVar v1) (TermVar v2)
  | AlphaConst : forall ctype1 content1 ctype2 content2,
      ctID ctype1 = ctID ctype2 ->
      (ctID ctype1 <> 0 \/ content1 = content2) ->
      term_alpha_eq (TermConst ctype1 content1) (TermConst ctype2 content2)
  | AlphaApply : forall lt1 rt1 lt2 rt2,
      term_alpha_eq lt1 lt2 -> term_alpha_eq rt1 rt2 ->
      term_alpha_eq (TermApply lt1 rt1) (TermApply lt2 rt2)
  | AlphaQuant : forall qtype1 qvar1 body1 qtype2 qvar2 body2,
      qtID qtype1 = qtID qtype2 ->
      (list_Z_eqb qvar1 qvar2 = true) /\ (term_alpha_eq body1 body2) \/
      (term_alpha_eq body1 (term_subst_v qvar1 qvar2 body2)) /\
      (term_alpha_eq (term_subst_v qvar2 qvar1 body1) body2) ->
      term_alpha_eq (TermQuant qtype1 qvar1 body1) (TermQuant qtype2 qvar2 body2). *)

Inductive term_alpha_eq : term -> term -> Prop :=
  | AlphaVar : forall v1 v2,
      v1 = v2 ->
      term_alpha_eq (TermVar v1) (TermVar v2)
  | AlphaConst : forall ctype1 content1 ctype2 content2,
      ctID ctype1 = ctID ctype2 ->
      (ctID ctype1 <> 0 \/ content1 = content2) ->
      term_alpha_eq (TermConst ctype1 content1) (TermConst ctype2 content2)
  | AlphaApply : forall lt1 rt1 lt2 rt2,
      term_alpha_eq lt1 lt2 -> term_alpha_eq rt1 rt2 ->
      term_alpha_eq (TermApply lt1 rt1) (TermApply lt2 rt2)
  | AlphaQuant : forall qtype1 qvar1 body1 qtype2 qvar2 body2,
      qtID qtype1 = qtID qtype2 ->
      (list_Z_eqb qvar1 qvar2 = true) /\ (term_alpha_eq body1 body2) \/
      (list_Z_eqb qvar1 qvar2 = false) /\ 
      (exists fresh,
        term_not_contain_var (TermQuant qtype1 qvar1 body1) fresh /\
        term_not_contain_var (TermQuant qtype2 qvar2 body2) fresh /\
        term_alpha_eq 
          (term_subst_v fresh qvar1 body1) 
          (term_subst_v fresh qvar2 body2)) ->
      term_alpha_eq (TermQuant qtype1 qvar1 body1) (TermQuant qtype2 qvar2 body2).

Fixpoint term_level (t : term) : nat :=
  match t with
  | TermVar _ => 0
  | TermConst _ _ => 0
  | TermApply t1 t2 => 
      1 + max (term_level t1) (term_level t2)
  | TermQuant _ _ body =>
      1 + term_level body
  end.

Lemma apply_level_l_lt : forall (t1 t2 : term),
  (term_level t1 < term_level (TermApply t1 t2))%nat.
Proof.
  intros; unfold term_level; fold term_level; lia.
Qed.

Lemma apply_level_r_lt : forall (t1 t2 : term),
  (term_level t2 < term_level (TermApply t1 t2))%nat.
Proof.
  intros; unfold term_level; fold term_level; lia.
Qed.

Lemma quant_level_lt : forall (qt : quant_type) (qv : var_name) (t : term),
  (term_level t < term_level (TermQuant qt qv t))%nat.
Proof.
  intros; unfold term_level; fold term_level; lia.
Qed.

Lemma subst_level_eq : forall (t : term) (str1 str2 : var_name),
  (term_level t = term_level (term_subst_v str1 str2 t))%nat.
Proof.
  induction t; try intros.
  + unfold term_subst_v.
    destruct list_Z_eqb; auto.
  + unfold term_subst_v; auto.
  + unfold term_subst_v; fold term_subst_v.
    unfold term_level; fold term_level.
    pose proof IHt1 str1 str2 as Ha; rewrite Ha.
    pose proof IHt2 str1 str2 as Hb; rewrite Hb.
    lia.
  + unfold term_subst_v; fold term_subst_v.
    destruct list_Z_eqb; auto.
    unfold term_level; fold term_level.
    pose proof IHt str1 str2 as Hx; rewrite Hx; auto.
Qed.


(* Lemma term_alpha_eq_var_eq : forall (v1 v2 : var_name),
  term_alpha_eq (TermVar v1) (TermVar v2) <-> (TermVar v1) = (TermVar v2).
Proof. *)

Lemma term_alpha_eq_refl : forall (t : term),
  term_alpha_eq t t.
Proof.
  induction t.
  + apply AlphaVar; reflexivity.
  + apply AlphaConst; [reflexivity | ].
    right; reflexivity.
  + apply AlphaApply; try auto.
  + apply AlphaQuant; [reflexivity | ].
    left; split; [ | apply IHt].
    apply list_Z_eq2eqb; reflexivity.
Qed.

Lemma term_alpha_eq_symm : forall (t1 t2 : term),
  term_alpha_eq t1 t2 ->
  term_alpha_eq t2 t1.
Proof.
  intros t1. 
  remember (term_level t1) as n.
  generalize dependent t1.
  induction n using lt_wf_ind.
  intros t1 Heqn t2 Halpha.
  destruct t1; destruct t2; try (inversion Halpha; fail).
  + inversion Halpha; subst; apply term_alpha_eq_refl.
  + inversion Halpha; subst; apply AlphaConst.
    rewrite H3; reflexivity.
    destruct H5; [left; rewrite <- H3; auto | right; rewrite H0; auto].
  + inversion Halpha; subst.
    pose proof apply_level_l_lt t1_1 t1_2 as Hsub1.
    pose proof apply_level_r_lt t1_1 t1_2 as Hsub2.
    pose proof H (term_level t1_1) Hsub1 t1_1.
    pose proof H (term_level t1_2) Hsub2 t1_2.
    apply AlphaApply.
    auto.
    auto.
  + inversion Halpha; subst; apply AlphaQuant.
    rewrite H2; reflexivity.
    destruct H7 as [[Haa Hab]|[Hba Hbb]]; [left | right].
    - split.
      * apply list_Z_eq2eqb.
        pose proof list_Z_eqb2eq qvar qvar0 Haa; auto.
      * pose proof quant_level_lt qtype qvar t1 as Hsub.
        pose proof H (term_level t1) Hsub t1.
        auto.
    - split.
      * apply list_Z_neq2neqb.
        pose proof list_Z_neqb2neq qvar qvar0 Hba; auto.
      * destruct Hbb as [x [Hxa [Hxb Hxc]]]; exists x.
        split; auto.  
        split; auto.
        pose proof subst_level_eq t1 x qvar as Heq.
        pose proof quant_level_lt qtype qvar t1 as Hsub.
        pose proof H (term_level (term_subst_v x qvar t1)).
        rewrite <- Heq in H0.
        pose proof H0 Hsub; auto.
Qed.

Lemma term_alpha_eq_trans : forall (t1 t2 t3 : term),
  term_alpha_eq t1 t2 ->
  term_alpha_eq t2 t3 ->
  term_alpha_eq t1 t3.
Proof.
  intros t1.
  remember (term_level t1) as n.
  generalize dependent t1.
  induction n using lt_wf_ind.
  intros t1 Heqn t2 t3 H12 H23.
  destruct t1; inversion H12; inversion H23; subst; try discriminate.
  + apply AlphaVar; inversion H4; auto.
  + apply AlphaConst; inversion H7; subst.
    rewrite H2, <- H5; reflexivity.
    rewrite H2 in H4.
    destruct (ctID ctype2) eqn:Hz.
    - destruct H4; congruence.
    - left; rewrite H2. 
      unfold not. intros H_contra. discriminate H_contra.
    - left; rewrite H2. 
      unfold not. intros H_contra. discriminate H_contra.
  + inversion H7; subst.
    pose proof apply_level_l_lt t1_1 t1_2 as Hsub1.
    pose proof apply_level_r_lt t1_1 t1_2 as Hsub2.
    assert (term_level t1_1 = term_level t1_1). { reflexivity. }
    assert (term_level t1_2 = term_level t1_2). { reflexivity. }
    pose proof H (term_level t1_1) Hsub1 t1_1 H0 lt2 lt3 H2 H5.
    pose proof H (term_level t1_2) Hsub2 t1_2 H1 rt2 rt3 H4 H6.
    apply AlphaApply; [auto | auto].
  + apply AlphaQuant; inversion H8; subst.
    lia.
    destruct H5 as [[Haa Hab]|[Hba Hbb]]; 
    destruct H7 as [[Hcc Hcd]|[Hdc Hdd]]; [left | right | right | ].
    - split.
      apply (list_Z_eqb_trans qvar qvar2 qvar3 Haa Hcc).
      assert (term_level t1 = term_level t1). {reflexivity. }
      pose proof quant_level_lt qtype qvar t1 as Hsub.
      pose proof H (term_level t1) Hsub t1 H0 body2 body3 Hab Hcd; auto.
    - pose proof list_Z_eqb2eq qvar qvar2 Haa as E; split.
      * rewrite E; auto.
      *       
Admitted.

#[export] Instance term_alpha_eq_refl': Reflexive term_alpha_eq.
Proof. unfold Reflexive. apply term_alpha_eq_refl. Qed.

#[export] Instance term_alpha_eq_symm': Symmetric term_alpha_eq.
Proof. unfold Symmetric. apply term_alpha_eq_symm. Qed.

#[export] Instance term_alpha_eq_trans': Transitive term_alpha_eq.
Proof. unfold Transitive. apply term_alpha_eq_trans. Qed.

#[export] Instance term_alpha_eq_equiv: Equivalence term_alpha_eq.
Proof.
  split.
  + apply term_alpha_eq_refl'.
  + apply term_alpha_eq_symm'.
  + apply term_alpha_eq_trans'.
Qed.

Lemma term_subst_v_same_name : forall (den src : var_name) (t : term),
  den = src ->
  term_subst_v den src t = t.
Proof.
  induction t.
  + intros.
    unfold term_subst_v; fold term_subst_v.
    rewrite <- H.
    destruct list_Z_eqb eqn:Heq; [ | reflexivity].
    apply list_Z_eqb2eq in Heq.
    rewrite Heq; reflexivity.
  + intros.
    unfold term_subst_v; fold term_subst_v.
    reflexivity.
  + intros.
    unfold term_subst_v; fold term_subst_v.
    pose proof IHt1 H.
    pose proof IHt2 H.
    rewrite H0, H1; reflexivity.
  + intros.
    unfold term_subst_v; fold term_subst_v.
    destruct (list_Z_eqb qvar src) eqn:Heq.
    - reflexivity.
    - pose proof IHt H; rewrite H0; reflexivity.
Qed.

Lemma subst_not_contains: forall (t : term) (v1 v2 : var_name),
  term_not_contain_var t v2 ->
  term_subst_v v1 v2 t = t.
Proof.
  induction t; try intros; try unfold term_subst_v; try fold term_subst_v. 
  + unfold term_not_contain_var in H.
    destruct (list_Z_eqb var v2) eqn:Heq; try pose proof list_Z_eqb2eq var v2 Heq.
    - congruence.
    - reflexivity.
  + unfold term_subst_v. reflexivity.
  + unfold term_not_contain_var in H; fold term_not_contain_var in H; destruct H.
    pose proof IHt1 v1 v2 H as Ha; rewrite Ha. 
    pose proof IHt2 v1 v2 H0 as Hb; rewrite Hb.
    reflexivity.
  + destruct (list_Z_eqb qvar v2) eqn:Heqq.
    - reflexivity.
    - unfold term_not_contain_var in H; fold term_not_contain_var in H.
      destruct H.
      pose proof IHt v1 v2 H0 as Ha; rewrite Ha; reflexivity.
Qed.

Lemma subst_not_free: forall (t : term) (v1 v2 : var_name),
  term_not_free_var t v2 ->
  term_subst_v v1 v2 t = t.
Proof.
  induction t; try intros; try unfold term_subst_v; try fold term_subst_v. 
  + unfold term_not_free_var in H.
    destruct (list_Z_eqb var v2) eqn:Heq; try pose proof list_Z_eqb2eq var v2 Heq.
    - congruence.
    - reflexivity.
  + unfold term_subst_v. reflexivity.
  + unfold term_not_free_var in H; fold term_not_free_var in H; destruct H.
    pose proof IHt1 v1 v2 H as Ha; rewrite Ha. 
    pose proof IHt2 v1 v2 H0 as Hb; rewrite Hb.
    reflexivity.
  + destruct (list_Z_eqb qvar v2) eqn:Heqq.
    - reflexivity.
    - unfold term_not_free_var in H; fold term_not_free_var in H.
      destruct H.
      * pose proof list_Z_neqb2neq _ _ Heqq; congruence.
      * destruct H as [Ha Hb].
        pose proof IHt v1 v2 Hb as Haa; rewrite Haa; reflexivity.
Qed.

(* Lemma alpha_equiv_subst_rev: forall (t : term) (v1 v2 : var_name),
  term_not_contain_var t v1 ->
  term_not_contain_var t v2 ->
  term_alpha_eq t (term_subst_v v1 v2 (term_subst_v v2 v1 t)).
Proof.
  induction t; try intros.
  + unfold term_subst_v.
    destruct list_Z_eqb eqn:Heq.
    - pose proof list_Z_eqb2eq var v1 Heq.
      destruct (list_Z_eqb v2 v2) eqn:He; try apply AlphaVar.
      * auto.
      * pose proof list_Z_eqb_refl v2; congruence.
    - destruct (list_Z_eqb var v2) eqn:He; [ | apply AlphaVar; reflexivity].
      unfold term_not_contain_var in *.
      pose proof list_Z_eqb2eq var v2 He.
      destruct H; congruence.
  + unfold term_subst_v; apply AlphaConst; [auto | auto].
  + unfold term_not_contain_var in H, H0; fold term_not_contain_var in H, H0.
    destruct H as [Ha Hb].
    destruct H0 as [H0a H0b].
    unfold term_subst_v; fold term_subst_v; apply AlphaApply.
    apply (IHt1 v1 v2 Ha H0a). 
    apply (IHt2 v1 v2 Hb H0b).
  + unfold term_not_contain_var in H, H0; fold term_not_contain_var in H, H0.
    unfold term_subst_v; fold term_subst_v.
Admitted.
(* destruct H as [Hc|[Ha Hb]];
    destruct H0 as [H0c|[H0a H0b]];
    destruct (list_Z_eqb qvar v1) eqn:Heq.
    - rewrite Hc in H0c.
      pose proof term_subst_v_same_name v1 v2 (TermQuant qtype qvar t) H0c.
      rewrite H; reflexivity.
    - pose proof list_Z_neqb2neq qvar v1 Heq; congruence.
    - unfold term_subst_v; fold term_subst_v.
      destruct (list_Z_eqb qvar v2) eqn:Heqq.
      * pose proof list_Z_eqb2eq qvar v2 Heqq; congruence.
      * apply AlphaQuant; [reflexivity | left; split; [pose proof list_Z_eqb_refl qvar; auto | ]].
        apply (IHt v1 v2 Hb H0b).
Qed. *) *)


(* must not_contain *)
(* t1 = ∃ y P(x, y, z) *)
(* t2 = ∃ u P(x, u, z) *)
(* str1 = y, str2 = x *)
Lemma alpha_equiv_same_rename: forall (t1 t2 : term) (str1 str2 : list Z),
  term_not_contain_var t1 str1 ->
  term_not_contain_var t2 str1 ->
  term_alpha_eq t1 t2 -> term_alpha_eq (term_subst_v str1 str2 t1) (term_subst_v str1 str2 t2).
Proof.
  intros t1. 
  remember (term_level t1) as n.
  generalize dependent t1.
  induction n using lt_wf_ind.
  intros t1 Heqn t2 v1 v2 Hn1 Hn2 Halpha.
  destruct t1; destruct t2; inversion Halpha; try subst; try unfold term_subst_v; 
  try unfold term_not_contain_var in Hn1, Hn2;
  try fold term_not_contain_var in Hn1, Hn2.
  + destruct list_Z_eqb; try apply AlphaVar; try reflexivity.
  + apply AlphaConst; [auto | auto].
  + fold term_subst_v; apply AlphaApply.
    - pose proof apply_level_l_lt t1_1 t1_2. 
      assert (term_level t1_1 = term_level t1_1). {reflexivity. }
      destruct Hn1 as [Hn1a Hn1b].
      destruct Hn2 as [Hn2a Hn2b].
      pose proof H (term_level t1_1) H0 t1_1 H1 t2_1 v1 v2 Hn1a Hn2a H3; auto.
    - pose proof apply_level_r_lt t1_1 t1_2.
      assert (term_level t1_2 = term_level t1_2). {reflexivity. }
      destruct Hn1 as [Hn1a Hn1b].
      destruct Hn2 as [Hn2a Hn2b].
      pose proof H (term_level t1_2) H0 t1_2 H1 t2_2 v1 v2 Hn1b Hn2b H5; auto.
  + fold term_subst_v.
    destruct H7 as [[Haa Hab]|[Hba Hbb]].
    - pose proof list_Z_eqb2eq qvar qvar0 Haa; rewrite H0.
      destruct (list_Z_eqb qvar0 v2) eqn:He.
      * apply AlphaQuant; [auto | left; split; [apply list_Z_eqb_refl | auto]].
      * apply AlphaQuant; [auto | left; split; [apply list_Z_eqb_refl | ]].
      pose proof quant_level_lt qtype qvar t1. 
      assert (term_level t1 = term_level t1). {reflexivity. }
      destruct Hn1 as [Hn1a Hn1b].
      destruct Hn2 as [Hn2a Hn2b].
      pose proof H (term_level t1) H1 t1 H3 t2 v1 v2 Hn1b Hn2b Hab; auto.
    - destruct (list_Z_eqb qvar v2) eqn:Hva;
      destruct (list_Z_eqb qvar0 v2) eqn:Hvb.
      * pose proof list_Z_eqb2eq qvar v2 Hva. 
        pose proof list_Z_eqb2eq qvar0 v2 Hvb.
        rewrite H0, H1 in Hba.
        congruence.
      * pose proof list_Z_eqb2eq qvar v2 Hva as HH; rewrite <- HH. 
        apply AlphaQuant; [auto | right; split; [auto | ]].
        destruct Hbb as [x [Hxa [Hxb Hxc]]]; exists x.
        split; auto.
        pose proof subst_level_eq t1 x qvar.
        pose proof quant_level_lt qtype qvar t1.
        assert (term_level (t1) =  term_level (t1)).
          { reflexivity. }
        pose proof H (term_level t1) H1 (t1) H3 (term_subst_v v1 v2 t2) x qvar.
        admit.
      * admit.
      * admit.  
Admitted. 

(* Lemma alpha_equiv_quant: forall (t1 t2 : term) (qt1 qt2 : quant_type) (qv1 qv2 : var_name), 
  term_alpha_eq (TermQuant qt1 qv1 t1) (TermQuant qt2 qv2 t2) /\ list_Z_eqb qv1 qv2 = true -> 
  term_alpha_eq t1 t2.
Proof.
  intros t1 t2 qt1 qt2 qv1 qv2 [Halpha Heqv].
  pose proof (list_Z_eqb2eq qv1 qv2 Heqv) as Hqveq.
  inversion Halpha; subst.
  destruct H6 as [[? ?]|[? ?]].
  + destruct H; auto.
  + rewrite Heqv in H. congruence.
Qed. *)

Lemma alpha_equiv_subst_trans: forall (t : term) (v1 v2 v3 : var_name),
  term_not_contain_var t v2 ->
  term_subst_v v3 v1 t = term_subst_v v3 v2 (term_subst_v v2 v1 t).
Proof.
  induction t; try intros.
  + unfold term_subst_v.
    destruct list_Z_eqb eqn:Heq.
    - pose proof list_Z_eqb2eq var v1 Heq.
      destruct (list_Z_eqb v2 v2) eqn:He; try apply AlphaVar.
      * auto.
      * pose proof list_Z_eqb_refl v2; congruence.
    - destruct (list_Z_eqb var v2) eqn:He; [ | reflexivity].
      unfold term_not_contain_var in *.
      pose proof list_Z_eqb2eq var v2 He.
      destruct H; congruence.
  + unfold term_subst_v; reflexivity.
  + unfold term_not_contain_var in H; fold term_not_contain_var in H.
    destruct H as [Ha Hb].
    unfold term_subst_v; fold term_subst_v.
    pose proof (IHt1 v1 v2 v3 Ha) as Haa; rewrite Haa. 
    pose proof (IHt2 v1 v2 v3 Hb) as Hbb; rewrite Hbb.
    reflexivity.
  + unfold term_not_contain_var in H; fold term_not_contain_var in H.
    unfold term_subst_v; fold term_subst_v.
    destruct H as [Ha Hb].
    destruct (list_Z_eqb qvar v1) eqn:Heq.
    - unfold term_subst_v; fold term_subst_v.
      destruct (list_Z_eqb qvar v2) eqn:Heqq.
      * pose proof list_Z_eqb2eq qvar v2 Heqq; congruence.
      * pose proof (subst_not_contains t v3 v2 Hb); rewrite H.
        reflexivity.
    - unfold term_subst_v; fold term_subst_v.
      destruct (list_Z_eqb qvar v2) eqn:Heqq.
      * pose proof list_Z_eqb2eq qvar v2 Heqq; congruence.
      * pose proof (IHt v1 v2 v3 Hb) as Hx; rewrite Hx.
        reflexivity.
Qed.

Lemma subst_not_contain: forall (t : term) (y qv x : var_name),
  x <> y ->
  term_not_contain_var t x ->
  term_not_contain_var t y ->
  term_not_contain_var (term_subst_v y qv t) x.
Proof.
  induction t; try intros; try unfold term_subst_v, term_not_contain_var in *.
  + destruct list_Z_eqb eqn:Heq; [auto | auto].
  + auto.
  + fold term_subst_v term_not_contain_var in *.
    destruct H0 as [Ha Hb]; destruct H1 as [Hc Hd].
    pose proof IHt1 y qv x H Ha Hc.
    pose proof IHt2 y qv x H Hb Hd.
    split; [auto | auto].
  + fold term_subst_v term_not_contain_var in *.
    destruct H0 as [Ha Hb]; destruct H1 as [Hc Hd].
    destruct (list_Z_eqb qvar qv) eqn:Heq.
    - unfold term_not_contain_var; fold term_not_contain_var.
      split; [auto | auto].
    - unfold term_not_contain_var; fold term_not_contain_var.
      pose proof IHt y qv x H Hb Hd. 
      split; [auto | auto].
Qed.

Lemma alpha_equiv_quant_allvar: forall (t1 t2 : term) (qt1 qt2 : quant_type) (qv1 qv2 x : var_name), 
  term_alpha_eq (TermQuant qt1 qv1 t1) (TermQuant qt2 qv2 t2) -> 
  term_not_contain_var (TermQuant qt1 qv1 t1) x ->
  term_not_contain_var (TermQuant qt2 qv2 t2) x ->
  list_Z_eqb qv1 qv2 = false -> 
  term_alpha_eq (term_subst_v x qv1 t1) (term_subst_v x qv2 t2).
Proof.
  intros.
  inversion H; subst.
  destruct H10 as [[Hla Hlb]|[Hra Hrb]].
  + destruct t1, t2; try inversion Hlb; try congruence.
  + destruct Hrb as [y [Hya [Hyb Hyc]]].
    destruct (list_Z_eqb x y) eqn:Hv.
    - pose proof list_Z_eqb2eq x y Hv.
      rewrite H3; auto.
    - pose proof list_Z_neqb2neq x y Hv.
      unfold term_not_contain_var in H0, H1, Hya, Hyb; fold term_not_contain_var in H0, H1, Hya, Hyb.
      destruct H0 as [Hba Hbb]; destruct H1 as [Hcaa Hcab];
      destruct Hya as [Hyaa Hyab]; destruct Hyb as [Hyba Hybb].
      pose proof alpha_equiv_subst_trans t1 qv1 y x Hyab.
      pose proof alpha_equiv_subst_trans t2 qv2 y x Hybb.
      rewrite H0.
      rewrite H1.
      apply (alpha_equiv_same_rename (term_subst_v y qv1 t1) (term_subst_v y qv2 t2) x y).
      * apply (subst_not_contain t1 y qv1 x H3 Hbb Hyab).
      * apply (subst_not_contain t2 y qv2 x H3 Hcab Hybb).
      * exact Hyc.
Qed.
(* 这个证明用到了 alpha_equiv_same_rename. 此 Lemma 被用在 return_wit_8_2 中 *)