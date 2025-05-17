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
Require Import String.
Local Open Scope string.

Import naive_C_Rules.
Local Open Scope sac.

Fixpoint sll {A: Type} (storeA: addr -> A -> Assertion) (x: addr) (l: list A) (struct_name data_name next_name: string): Assertion :=
  match l with
    | nil     => [| x = NULL |] && emp
    | a :: l0 => [| x <> NULL |] && 
                 EX h y: addr,
                   &(x # struct_name ->ₛ data_name) # Ptr |-> h **
                   &(x # struct_name ->ₛ next_name) # Ptr |-> y **
                   storeA h a **
                   sll storeA y l0 struct_name data_name next_name
  end.

Fixpoint sllseg {A : Type} (storeA : addr -> A -> Assertion) (x : addr) (y : addr) (l : list A) (struct_name data_name next_name: string): Assertion :=
  match l with
    | nil     => [| x = y |] && emp
    | a :: l0 => [| x <> NULL |] && 
                 EX h q: addr,
                   &(x # struct_name ->ₛ data_name) # Ptr |-> h **
                   &(x # struct_name ->ₛ next_name) # Ptr |-> q **
                   storeA h a **
                   sllseg storeA q y l0 struct_name data_name next_name
  end.

Fixpoint sllbseg {A : Type} (storeA : addr -> A -> Assertion) (x y: addr) (l: list A) (struct_name data_name next_name: string): Assertion :=
  match l with
    | nil     => [| x = y |] && emp
    | a :: l0 => EX z h: addr,
                   [| z <> NULL |] && 
                   x # Ptr |-> z **
                   &(z # struct_name ->ₛ data_name) # Ptr |-> h **
                   storeA h a **
                   sllbseg storeA (&(z # struct_name ->ₛ next_name)) y l0 struct_name data_name next_name
  end.


Definition append {A : Type} (l1 : list A) (l2 : list A) := app l1 l2.

Lemma sll_zero: forall A (storeA: addr -> A -> Assertion) x l s d n,
  x = NULL ->
  sll storeA x l s d n |-- [| l = nil |] && emp.
Proof.
  intros.
  destruct l.
  + entailer!.
  + simpl.
    Intros x0 x1.
    entailer!.
Qed.

Lemma sll_not_zero: forall A (storeA: addr -> A -> Assertion) x l s d n,
  x <> NULL ->
  sll storeA x l s d n |--
    EX h y a l0,
      [| l = a :: l0 |] &&
      &(x # s ->ₛ d) # Ptr |-> h **
      &(x # s ->ₛ n) # Ptr |-> y **
      storeA h a **
      sll storeA y l0 s d n.
Proof.
  intros.
  destruct l.
  + simpl.
    Intros.
    tauto.
  + simpl.
    Intros h y.
    Exists h y a l.
    entailer!.
Qed.

Lemma sll_not_zero': forall A (storeA: addr -> A -> Assertion) x l s d n,
  x <> NULL ->
  sll storeA x l s d n |-- [| l <> nil |].
Proof.
  intros.
  destruct l.
  + simpl.
    Intros.
    tauto.
  + simpl. Intros.
    Intros y.
    entailer!.
    congruence.
Qed.

Lemma sllseg_len1: forall {A: Type} (x y: addr) (a: A) (storeA : addr -> A -> Assertion) s d n,
  x <> NULL ->
  EX h: addr,
  &(x # s ->ₛ d) # Ptr |-> h **
  &(x # s ->ₛ n) # Ptr |-> y **
  storeA h a  |--
  sllseg storeA x y (a :: nil) s d n.
Proof.
  intros.
  pre_process.
  Intros h.
  simpl sllseg.
  Exists h y.
  entailer!.
Qed.

Lemma sllseg_sllseg: forall A (storeA: addr -> A -> Assertion) x y z l1 l2 s d n,
  sllseg storeA x y l1 s d n ** sllseg storeA y z l2 s d n |--
  sllseg storeA x z (l1 ++ l2) s d n.
Proof.
  intros.
  revert x; induction l1; simpl sllseg; intros.
  + Intros.
    subst y.
    entailer!.
  + Intros. Intros z0.
    Intros q.
    Exists z0.
    entailer!.
    Exists q.
    sep_apply IHl1.
    entailer!.
Qed.

Lemma sllseg_sll: forall A (storeA: addr -> A -> Assertion) x y l1 l2 s d n,
  sllseg storeA x y l1 s d n ** sll storeA y l2 s d n |--
  sll storeA x (l1 ++ l2) s d n.
Proof.
  intros.
  revert x; induction l1; simpl sllseg; simpl sll; intros.
  + Intros.
    subst y.
    entailer!.
  + Intros. Intros z0 q.
    Exists z0 q.
    sep_apply IHl1.
    entailer!.
Qed.

Lemma sllbseg_2_sllseg: forall A (storeA: addr -> A -> Assertion) x y z l s d n,
  sllbseg storeA x y l s d n ** y # Ptr |-> z |--
  EX y': addr, x # Ptr |-> y' ** sllseg storeA y' z l s d n.
Proof.
  intros.
  revert x; induction l; simpl; intros.
  + Intros.
    subst x.
    Exists z; entailer!.
  + Intros x_v.
    Exists x_v.
    Intros q.
    Exists q.
    entailer!.
    sep_apply IHl.
    Intros y'.
    Exists y'.
    entailer!.
Qed.

Lemma sllbseg_len1: forall A (storeA: addr -> A -> Assertion) (x y: addr) (a: A) s d n,
  y <> 0 ->
  EX h: addr,
  x # Ptr |-> y **
  &( y # s ->ₛ d) # Ptr |-> h **
  storeA h a |--
  sllbseg storeA x (&( y # s ->ₛ n)) (a :: nil) s d n.
Proof.
  intros.
  simpl.
  Exists y.
  Intros h.
  Exists h.
  entailer!.
Qed.

Lemma sllbseg_sllbseg: forall A (storeA: addr -> A -> Assertion) x y z l1 l2 s d n,
  sllbseg storeA x y l1 s d n ** sllbseg storeA y z l2 s d n |--
  sllbseg storeA x z (l1 ++ l2) s d n.
Proof.
  intros.
  revert x; induction l1; simpl; intros.
  + entailer!.
    subst x.
    entailer!.
  + Intros u.
    Exists u.
    Intros h.
    Exists h.
    entailer!.
Qed.

Lemma sllseg_0_sll: forall A (storeA: addr -> A -> Assertion) x l s d n,
  sllseg storeA x 0 l s d n |-- sll storeA x l s d n.
Proof.
  intros. revert x. 
  induction l; try easy.
  simpl. intros.
  Intros.
  Intros h.
  Intros q.
  Exists h q.
  entailer!.
Qed.

Definition sll_para {A: Type} (storeA: addr -> A -> Assertion): Prop := True.
