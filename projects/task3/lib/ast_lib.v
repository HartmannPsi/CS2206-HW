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

<<<<<<< HEAD
(* Option *)
(* 
Inductive Option (A : Type) : Type :=
| Some : A -> Option A
| None : Option A.

Arguments Some {A} _.
Arguments None {A}.

Definition Option_map {A B : Type} (f : A -> B) (opt : Option A) : Option B :=
  match opt with
  | Some x => Some (f x)
  | None => None
  end.

Definition Option_bind {A B} (opt : Option A) (f : A -> Option B) : Option B :=
  match opt with
  | Some x => f x
  | None => None
  end.

Definition Option_make {A} (x : A) : Option A := Some x.

Definition Option_unwrap {A : Type} (default : A) (opt : Option A) : A :=
  match opt with
  | Some x => x
  | None => default
  end.

Definition is_some {A : Type} (opt : Option A): bool :=
  match opt with
  | Some x => true
  | None => false
  end.
*)

=======
>>>>>>> 712800f12df37138aa21886047f3c479742fcb8b
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
    | SRBool ans => &(x # "solve_res" ->ₛ "d" .ₛ "ans") # Int |-> ans
    | SRTList l => EX y: addr,
                   &(x # "solve_res" ->ₛ "d" .ₛ "list") # Ptr |-> y **
                   sll_term_list y l
  end.

Definition store_solve_res' (x: addr) (sr: solve_res): Assertion :=
  match sr with
    | SRBool ans => [| x <> NULL |] && &(x # "solve_res" ->ₛ "d" .ₛ "ans") # Int |-> ans
    | SRTList l => [| x <> NULL |] && EX y: addr,
                   &(x # "solve_res" ->ₛ "d" .ₛ "list") # Ptr |-> y **
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
  &(x # "solve_res" ->ₛ "d" .ₛ "ans") # Int |-> ans.
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
    &(x # "solve_res" ->ₛ "d" .ₛ "list") # Ptr |-> y **
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

(* about list Z *)

Fixpoint list_Z_eqb (l1 l2 : list Z) : bool :=
  match l1, l2 with
  | [], [] => true
  | x1 :: t1, x2 :: t2 => Z.eqb x1 x2 && list_Z_eqb t1 t2
  | _, _ => false
  end.

Definition list_Z_cmp (l1 l2 : list Z) : Z :=
  if list_Z_eqb l1 l2 then 0 else 1.

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

(* subst *)

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

(* alpha_equiv *)

Fixpoint term_alpha_eq (t1 t2 : term) : bool :=
  match t1, t2 with
  | TermVar v1, TermVar v2 => 
      if (list_Z_eqb v1 v2) then true else false
  | TermConst ctype1 content1, TermConst ctype2 content2 =>
      if Z.eqb (ctID ctype1) (ctID ctype2) then
        if Z.eqb (ctID ctype1) 0 then
          if Z.eqb content1 content2 then true else false
        else
          true
      else
        false
  | TermApply lt1 rt1, TermApply lt2 rt2 =>
      term_alpha_eq lt1 lt2 && term_alpha_eq rt1 rt2
  | TermQuant qtype1 qvar1 body1, TermQuant qtype2 qvar2 body2 =>
      if Z.eqb (qtID qtype1) (qtID qtype2) then
        term_alpha_eq body1 (term_subst_v qvar1 qvar2 body2)
      else
        false
  | _, _ => false
  end.

Definition term_alpha_eqn (t1 t2 : term) : Z :=
  if term_alpha_eq t1 t2 then 1 else 0.

(* thm_apply *)

Definition term_res: Type := option term.
Definition imply_res: Type := option ImplyProp.

Definition imply_res_Cont (assum concl: term) : imply_res :=
  Some (ImplP assum concl).

Inductive partial_quant: Type :=
  | NQuant : partial_quant
  | PQuant (qt: quant_type) (x: var_name) (pq: partial_quant) : partial_quant.

Fixpoint store_partial_quant (rt fin: addr) (pq: partial_quant) : Assertion :=
  match pq with
  | NQuant => [| rt = fin |] && emp
  | PQuant qt x t => EX y z: addr,
                &(rt # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type") # Int |-> qtID qt **
                &(rt # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var") # Ptr |-> y **
                &(rt # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body") # Ptr |-> z **
                store_string y x ** store_partial_quant z fin t
  end.

Definition store_term_res (x: addr) (t: term_res): Assertion :=
  match t with
  | Some ti => store_term x ti
  | None => [| x = NULL |]
  end.

Definition store_imply_res (x: addr) (impl: imply_res): Assertion :=
  match impl with
  | Some (ImplP assum concl) => EX y z:addr,
              store_ImplyProp x y z assum concl
  | None => [| x = NULL |]
  end.

Fixpoint thm_subst_rem (thm: term) (l: var_sub_list): bool * partial_quant :=
  match l with 
    | nil => (true, NQuant)
    | (VarSub v t) :: l0 => 
      match thm with
        | TermQuant qt v' body =>
            let (s, p) := thm_subst_rem body l0 in
            (s, PQuant qt v' p)
        | _ => (false, NQuant)
      end
  end.

Fixpoint thm_subst (thm: term) (l: var_sub_list): bool * term :=
  match l with 
    | nil => (true, thm)
    | (VarSub v t) :: l0 => 
      match thm with
        | TermQuant qt v' body =>
            thm_subst (term_subst_t t v' body) l0
        | _ => (false, thm)
      end
  end.

Definition store_sub_thm_res (rt fin: addr) (thm: term) (l: var_sub_list): Assertion :=
  let (s1, pq) := thm_subst_rem thm l in let (s2, t) := thm_subst thm l in
  match (s1, s2) with
    | (true, true) => store_partial_quant rt fin pq ** store_term fin t
    | (false, false) => store_partial_quant rt fin pq ** store_term fin t (* fin may be 0 *)
    | _ => [| False |] && emp
  end.

Definition sep_impl (t : term): imply_res :=
  match t with
    | TermApply (TermApply (TermConst CImpl c) r) tr => 
      Some (ImplP r tr)
    | _ => None
  end.

Fixpoint gen_pre (thm target : term): term_list :=
  if term_alpha_eq thm target then
    nil
  else
    match thm with 
    | TermApply (TermApply (TermConst CImpl c) r) tr =>
      r :: gen_pre tr target
    | _ => nil
  end.

Definition thm_app (thm : term) (l : var_sub_list) (goal : term): solve_res :=
  match thm_subst thm l with
  | (false, _) => SRBool 0
  | (true, thm_ins) =>
      if term_alpha_eq thm_ins goal then SRBool 1
      else SRTList (gen_pre thm_ins goal)
  end.

(* Lemmas *)

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
<<<<<<< HEAD

Inductive partial_quant: Type :=
  | NQuant : partial_quant
  | PQuant (qt: quant_type) (x: var_name) (pq: partial_quant) : partial_quant.

Fixpoint store_partial_quant (rt fin: addr) (pq: partial_quant) : Assertion :=
  match pq with
  | NQuant => [| rt = fin |] && emp
  | PQuant qt x t => EX y z: addr,
                &(rt # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type") # Int |-> qtID qt **
                &(rt # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var") # Ptr |-> y **
                &(rt # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body") # Ptr |-> z **
                store_string y x ** store_partial_quant z fin t
  end.

Fixpoint thm_subst_rem (thm: term) (l: var_sub_list): option partial_quant :=
  match l with 
    | nil => Some NQuant
    | (VarSub v t) :: l0 => 
      match thm with
        | TermQuant qt v' body =>
            match thm_subst_rem body l0 with
            | Some p => Some (PQuant qt v' p)
            | None => None
            end
        | _ => None
      end
  end.

(* 
Definition sub_thm_mem (thm: term) (l: var_sub_list) (ret: term) :=
*)

(* Fixpoint thm_subst (thm: term) (l: var_sub_list): bool * term :=
  match l with 
    | nil => (true, thm)
    | (VarSub v t) :: l0 => 
      match thm with
        | TermQuant qt v' body =>
            thm_subst (term_subst_t t v' body) l0
        | _ => (false, thm)
      end
  end. *)

(* Definition store_sub_thm_res (rt fin: addr) (thm: term) (l: var_sub_list): Assertion :=
  let (s1, pq) := thm_subst_rem thm l in let (s2, t) := thm_subst thm l in
  match (s1, s2) with
    | (true, true) => store_partial_quant rt fin pq ** store_term fin t
    | (false, false) => [||] EEX y store_partial_quant rt fin pq ** store_term fin t
    | _ => [| False |] && emp
  end. *)
=======
>>>>>>> 712800f12df37138aa21886047f3c479742fcb8b
