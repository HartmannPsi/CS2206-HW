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

Lemma list_Z_eqb_refl : forall (l : list Z),
  list_Z_eqb l l = true.
Proof.
  intros.
  apply list_Z_eqb_eq.
  reflexivity.
Qed.

Lemma list_Z_eqb_symm : forall (l1 l2 : list Z),
  list_Z_eqb l1 l2 = true ->
  list_Z_eqb l2 l1 = true.
Proof.
  intros.
  apply list_Z_eqb_eq.
  pose proof list_Z_eqb2eq l1 l2 H.
  auto.
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

Fixpoint term_not_contain_var (t : term) (var : var_name) : Prop :=
  match t with
  | TermVar v => v <> var
  | TermConst _ _ => True
  | TermApply lt rt => term_not_contain_var lt var /\ term_not_contain_var rt var
  | TermQuant _ qvar body => qvar <> var /\ term_not_contain_var body var
  end.

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
      (exists fresh,
        term_not_contain_var (TermQuant qtype1 qvar1 body1) fresh /\
        term_not_contain_var (TermQuant qtype2 qvar2 body2) fresh /\
        term_alpha_eq 
          (term_subst_v fresh qvar1 body1) 
          (term_subst_v fresh qvar2 body2)) ->
      term_alpha_eq (TermQuant qtype1 qvar1 body1) (TermQuant qtype2 qvar2 body2).

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
  induction t1, t2; try intros; try inversion H.
  + apply AlphaVar. auto.
  + apply AlphaConst.
    auto.
    destruct H5.
    - left; rewrite <- H3; auto.
    - right; auto.
  + apply AlphaApply.  
    pose proof IHt1_1 t2_1 H3.
    pose proof IHt1_2 t2_2 H5.
    auto. auto.
  + apply AlphaQuant; [ auto | ].
    destruct H7.
    - destruct H7.
      pose proof list_Z_eqb2eq qvar qvar0 H7.
      rewrite H9.
      pose proof IHt1 t2.
      left.
      split.
      * apply list_Z_eq2eqb; reflexivity.
      * apply H10, H8.
    - right.
      destruct H7 as [x [Ha [Hb Hc]]].
      exists x.
      split; [exact Hb | split; [exact Ha | ]].
      induction (term_subst_v x qvar t1), (term_subst_v x qvar0 t2); try inversion Hc.
      * apply AlphaVar; auto.
      * apply AlphaConst; try auto.
        rewrite <- H10.
        destruct H12; [left; auto | right; auto].
      * apply AlphaApply. admit. admit.
      * apply AlphaQuant; [auto | ].
        destruct H14.
          
      fold term_subst_v.
Admitted.

Lemma term_alpha_eq_trans : forall (t1 t2 t3 : term),
  term_alpha_eq t1 t2 ->
  term_alpha_eq t2 t3 ->
  term_alpha_eq t1 t3.
Proof.
Admitted.

Lemma term_subst_v_same_name : forall (den src : var_name) (t : term),
  list_Z_eqb den src = true ->
  term_alpha_eq (term_subst_v den src t) t.
Proof.
  induction t.
  + intros.
    unfold term_subst_v; fold term_subst_v.
    apply list_Z_eqb2eq in H.
    rewrite <- H.
    destruct list_Z_eqb eqn:Heq; [ | apply term_alpha_eq_refl].
    apply list_Z_eqb2eq in Heq.
    rewrite Heq.
    apply term_alpha_eq_refl.
  + intros.
    unfold term_subst_v; fold term_subst_v.
    apply term_alpha_eq_refl.
  + intros.
    unfold term_subst_v; fold term_subst_v.
    apply AlphaApply.
    auto. auto.
  + intros.
    unfold term_subst_v; fold term_subst_v.
    destruct (list_Z_eqb qvar src) eqn:Heq.
    - apply term_alpha_eq_refl.
    - apply AlphaQuant; [reflexivity | ].
      left. split.
      * apply list_Z_eq2eqb; reflexivity.
      * apply IHt, H.
Qed.

Lemma alpha_equiv_same_rename: forall (t1 t2 : term) (str1 str2 : list Z),
  term_alpha_eq t1 t2 -> term_alpha_eq (term_subst_v str1 str2 t1) (term_subst_v str1 str2 t2).
Proof.
  induction t2,t1; try intros.
Admitted. 

(* mal-defined term_eq *)

Fixpoint term_eq (t1 t2: term) : bool :=
  match t1, t2 with
  | TermVar v1, TermVar v2 => 
      list_Z_eqb v1 v2
  | TermConst ctype1 content1, TermConst ctype2 content2 =>
      (Z.eqb (ctID ctype1) (ctID ctype2)) && 
      ((negb (Z.eqb (ctID ctype1) 0)) || (Z.eqb content1 content2)) 
  | TermApply lt1 rt1, TermApply lt2 rt2 =>
      term_eq lt1 lt2 && term_eq rt1 rt2
  | TermQuant qtype1 qvar1 body1, TermQuant qtype2 qvar2 body2 =>
      (Z.eqb (qtID qtype1) (qtID qtype2)) && (list_Z_eqb qvar1 qvar2) &&
      term_eq body1 body2
  | _, _ => false
  end.

Lemma term_eq_refl: forall t,
  term_eq t t = true.
Proof.
  induction t.
  + unfold term_eq; apply list_Z_eq2eqb; reflexivity.
  + unfold term_eq; rewrite andb_true_iff.
    split.
    - rewrite Z.eqb_eq; reflexivity.
    - rewrite orb_true_iff.
      right.
      rewrite Z.eqb_eq; reflexivity.
  + unfold term_eq; fold term_eq.
    rewrite andb_true_iff.
    auto.
  + unfold term_eq; fold term_eq.
    rewrite andb_true_iff.
    rewrite andb_true_iff.
    split. split.
    - rewrite Z.eqb_eq; reflexivity.
    - apply list_Z_eq2eqb; reflexivity.
    - auto.
Qed.  

Lemma term_eq_symm: forall t1 t2,
  term_eq t1 t2 = true -> term_eq t2 t1 = true.
Proof.
  induction t1,t2; try discriminate.
  + unfold term_eq.
    apply list_Z_eqb_symm.
  + unfold term_eq.
    rewrite andb_true_iff.
    rewrite orb_true_iff.
    intros.
    rewrite andb_true_iff.
    rewrite orb_true_iff.
    destruct H as [Ha [Hb|Hc]].
    - split.
      * rewrite Z.eqb_eq in *; auto.
      * rewrite negb_true_iff in *.
        rewrite Z.eqb_eq in Ha.
        rewrite <- Ha.
        left; auto.
    - split.
      * rewrite Z.eqb_eq in *; auto.
      * rewrite Z.eqb_eq in *.
        right; auto.
  + unfold term_eq in * ; fold term_eq in *.
    rewrite andb_true_iff.
    rewrite andb_true_iff.
    intros.
    destruct H as [Ha Hb].
    pose proof IHt1_1 t2_1 Ha.
    pose proof IHt1_2 t2_2 Hb.
    auto.
  + unfold term_eq in * ; fold term_eq in *.
    repeat rewrite andb_true_iff in *.
    intros.
    destruct H as [[Ha Hb] Hc].
    rewrite Z.eqb_eq in *.
    split. split.
    - auto.
    - apply list_Z_eqb_symm; auto.
    - apply (IHt1 t2 Hc).
Qed.

Lemma term_eq_trans: forall t1 t2 t3,
  term_eq t1 t2 = true ->
  term_eq t2 t3 = true ->
  term_eq t1 t3 = true.
Proof.
  intros t1 t2.
  revert t1.
  induction t2.
  + destruct t1, t3; try discriminate.
    unfold term_eq.
    apply list_Z_eqb_trans.
  + destruct t1, t3; try discriminate.
    unfold term_eq.
    repeat rewrite andb_true_iff, orb_true_iff.
    rewrite Z.eqb_eq.
    intros.
    destruct H as [Ha [Hb|Hc]].
    rewrite Ha in *.
    destruct H0 as [H1a [H1b|H1c]].
    - split; auto.
    - split; auto.
    - destruct H0 as [H1a [H1b|H1c]].
      * repeat rewrite negb_true_iff, Z.eqb_eq, Z.eqb_neq in *.
        split. rewrite Ha, H1a; reflexivity.
        left; rewrite Ha; auto.
      * repeat rewrite negb_true_iff, Z.eqb_eq, Z.eqb_neq in *.
        split. rewrite Ha, H1a; reflexivity.
        right. rewrite Z.eqb_eq, Hc, H1c; reflexivity.
  + destruct t1, t3; try discriminate.
    unfold term_eq; fold term_eq.
    intros.
    repeat rewrite andb_true_iff in *.
    destruct H, H0.
    split.
    apply (IHt2_1 t1_1 t3_1 H H0).
    apply (IHt2_2 t1_2 t3_2 H1 H2).
  + destruct t1, t3; try discriminate.
    unfold term_eq; fold term_eq.
    intros.
    repeat rewrite andb_true_iff in *.
    destruct H, H0.
    destruct H, H0.
    split. split.
    - rewrite Z.eqb_eq in *.
      rewrite H, H0; reflexivity.
    - apply (list_Z_eqb_trans qvar0 qvar qvar1); try auto.
    - apply (IHt2 t1 t3 H1 H2). 
Qed.
