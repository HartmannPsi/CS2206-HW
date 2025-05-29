#include "cnf_trans.h"

#include "int_array_def.h"
#include "verification_list.h"
#include "verification_stdlib.h"

/*@ Import Coq Require Import smt_lang_lib */
/*@ Import Coq Require Import cnf_trans_lib */

/*@ Extern Coq (SmtProp :: *) */
/*@ Extern Coq (PreData :: *) */
/*@ Extern Coq (SmtPropBop :: *) */
/*@ Extern Coq (SmtPropUop :: *) */
/*@ Extern Coq (store_SmtProp : Z -> SmtProp -> Assertion)
               (store_SmtProp' : Z -> SmtProp -> Assertion)
               (store_SmtProp_cell : Z -> SmtProp -> Assertion)
               (sll_SmtProplist : Z -> list SmtProp -> Assertion)
               (sllseg_SmtProplist : Z -> list SmtProp -> Assertion)
               (sllbseg_SmtProplist : Z -> list SmtProp -> Assertion)
               (init_int_array : Z -> Z -> Assertion)
               (store_int_array : Z -> Z -> list Z -> Assertion)
               (store_cnf_list_cell : Z -> list Z -> Assertion)
               (sll_cnf_list : Z -> list (list Z) -> Assertion)
               (sllseg_cnf_list : Z -> list (list Z) -> Assertion)
               (sllbseg_cnf_list : Z -> list (list Z) -> Assertion)
               (store_predata : Z -> list (list Z) -> Z -> Z -> Assertion)
               (iff2cnf_binary : Z -> Z -> Z -> Z -> list (list Z))
               (iff2cnf_unary : Z -> Z -> list (list Z))
               (iff2cnf_length_binary : Z -> Z -> Z -> Z -> Z)
               (SmtPBID : SmtPropBop -> Z)
               (SmtPUID : SmtPropUop -> Z)
               (all_zero_list : Z -> list Z)
               (prop_cnt_inf : list (list Z) -> Z)
               */

/* BEGIN Given Functions */

// 分配一个大小为size的全零的int数组
int *malloc_int_array(int size)
    /*@ Require size > 0
        Ensure __return != 0 &&
               store_int_array(__return, size, all_zero_list(size))
     */
    ;

// 释放int数组
void free_int_array(int *array)
    /*@ Require exists n, array != 0 && n > 0 &&
                  store_undef_int_array(array, n)
      Ensure emp
    */
    ;

// 分配一个初始全零 cnf_list 结构体
cnf_list *malloc_cnf_list()
    /*@ Require emp
        Ensure __return != 0 &&
               data_at(&(__return -> size), 0) *
               data_at(&(__return -> clause), 0) *
               data_at(&(__return -> next), 0)
      */
    ;

// 释放 cnf_list 结构体
void free_cnf_list(cnf_list *list)
    /*@ Require exists l, sll_cnf_list(list, l)
        Ensure emp
      */
    ;

/* END Given Functions */

void clause_gen_unary(int p2, int p3, PreData *data)
/*@ With clist pcnt ccnt
      Require p2 != 0 && p3 != 0 &&
              store_predata(data, clist, pcnt, ccnt)
      Ensure store_predata(data, app(iff2cnf_unary(p2, p3),
   clist), pcnt, ccnt + 2)
*/
{
  int size = 3;
  int *clause1 = malloc_int_array(size);
  int *clause2 = malloc_int_array(size);
  // 完成 SET_PROP: p3<->(p1 op p2) / p3<->not p2

  // p3\/p2
  clause1[0] = p2;
  clause1[1] = p3;
  // 非p3\/非p2
  clause2[0] = -p2;
  clause2[1] = -p3;

  cnf_list *list1 = malloc_cnf_list();
  cnf_list *list2 = malloc_cnf_list();
  list1->size = size;
  list2->size = size;
  list1->clause = clause1;
  list2->clause = clause2;

  list1->next = list2;

  /*@ store_predata(data@pre, clist, pcnt, ccnt)
      which implies
      data@pre != 0 && Zlength(clist) == ccnt && prop_cnt_inf(clist) == pcnt &&
      exists y,
        data_at(&(data@pre -> cnf_res), y) *
        data_at(&(data@pre -> prop_cnt), pcnt) *
        data_at(&(data@pre -> clause_cnt), ccnt) *
        sll_cnf_list(y, clist)
   */

  list2->next = data->cnf_res;
  data->cnf_res = list1;
  data->clause_cnt += 2;
}

// 生成p3<->(p1 op p2)对应的cnf中的clause
// p3<->not p2 (op为 not时， 此时p1缺省为0)
void clause_gen_binary(int p1, int p2, int p3, int op, PreData *data)
/*@ With clist pcnt ccnt
      Require p1 != 0 && p2 != 0 && p3 != 0 &&
              store_predata(data, clist, pcnt, ccnt)
      Ensure store_predata(data, app(iff2cnf_binary(p1, p2, p3, op),
   clist), pcnt, ccnt + iff2cnf_length_binary(p1, p2, p3, op))
*/
{
  int size = 3;
  int *clause1 = malloc_int_array(size);
  int *clause2 = malloc_int_array(size);
  int *clause3 = malloc_int_array(size);
  int *clause4 = malloc_int_array(size);
  // 完成 SET_PROP: p3<->(p1 op p2) / p3<->not p2
  int cnt = 0;
  switch (op) {
    case SMTPROP_OR: {
      // p3\/非p1
      clause1[0] = -p1;
      clause1[1] = p3;
      // p3\/非p2
      clause2[0] = -p2;
      clause2[1] = p3;
      if (p1 != p2) {
        // 非p3\/p1\/p2
        clause3[0] = p1;
        clause3[1] = p2;
        clause3[2] = -p3;
      } else {
        clause3[0] = p1;
        clause3[1] = -p3;
      }
      cnt += 3;
      break;
    }
    case SMTPROP_AND: {
      // 非p3\/p1
      clause1[0] = p1;
      clause1[1] = -p3;
      // 非p3\/p2
      clause2[0] = p2;
      clause2[1] = -p3;
      if (p1 != p2) {
        // p3\/非p1\/非p2
        clause3[0] = -p1;
        clause3[1] = -p2;
        clause3[2] = p3;
      } else {
        clause3[0] = -p1;
        clause3[1] = p3;
      }
      cnt += 3;
      break;
    }
    case SMTPROP_IMPLY: {
      if (p1 != p2) {
        // p3\/p1
        clause1[0] = p1;
        clause1[1] = p3;
        // p3\/非p2
        clause2[0] = -p2;
        clause2[1] = p3;
        // 非p3\/非p1\/p2
        clause3[0] = -p1;
        clause3[1] = p2;
        clause3[2] = -p3;
        cnt += 3;
      } else {
        clause1[0] = p3;
        cnt += 1;
      }
      break;
    }
    case SMTPROP_IFF: {
      if (p1 != p2) {
        // p3\/p1\/p2
        clause1[0] = p1;
        clause1[1] = p2;
        clause1[2] = p3;
        // p3\/非p1\/非p2
        clause2[0] = -p1;
        clause2[1] = -p2;
        clause2[2] = p3;
        // 非p3\/p1\/非p2
        clause3[0] = p1;
        clause3[1] = -p2;
        clause3[2] = -p3;
        // 非p3\/非p1\/p2
        clause4[0] = -p1;
        clause4[1] = p2;
        clause4[2] = -p3;
        cnt += 4;
      } else {
        clause1[0] = p3;
        cnt += 1;
      }
      break;
    }
    default: {
      // unreachable
    }
  }
  cnf_list *list1 = malloc_cnf_list();
  cnf_list *list2 = malloc_cnf_list();
  cnf_list *list3 = malloc_cnf_list();
  cnf_list *list4 = malloc_cnf_list();
  list1->size = size;
  list2->size = size;
  list3->size = size;
  list4->size = size;
  list1->clause = clause1;
  list2->clause = clause2;
  list3->clause = clause3;
  list4->clause = clause4;

  /*@ store_predata(data@pre, clist, pcnt, ccnt)
    which implies
    data@pre != 0 && Zlength(clist) == ccnt && prop_cnt_inf(clist) == pcnt &&
    exists y,
      data_at(&(data@pre -> cnf_res), y) *
      data_at(&(data@pre -> prop_cnt), pcnt) *
      data_at(&(data@pre -> clause_cnt), ccnt) *
      sll_cnf_list(y, clist)
 */

  if (cnt == 1) {
    list1->next = data->cnf_res;
    data->cnf_res = list1;
    data->clause_cnt += 1;
    free_int_array(clause2);
    free_int_array(clause3);
    free_int_array(clause4);
    free_cnf_list(list2);
    free_cnf_list(list3);
    free_cnf_list(list4);
  } else if (cnt == 2) {
    list1->next = list2;
    list2->next = data->cnf_res;
    data->cnf_res = list1;
    data->clause_cnt += 2;
    free_int_array(clause3);
    free_int_array(clause4);
    free_cnf_list(list3);
    free_cnf_list(list4);
  } else if (cnt == 3) {
    list1->next = list2;
    list2->next = list3;
    list3->next = data->cnf_res;
    data->cnf_res = list1;
    data->clause_cnt += 3;
    free_int_array(clause4);
    free_cnf_list(list4);
  } else {
    list1->next = list2;
    list2->next = list3;
    list3->next = list4;
    list4->next = data->cnf_res;
    data->cnf_res = list1;
    data->clause_cnt += 4;
  }
}

int prop2cnf(SmtProp *p, PreData *data) {
  int res = 0;
  switch (p->type) {
    case SMTB_PROP: {
      int p1 = prop2cnf(p->prop.Binary_prop.prop1, data);
      int p2 = prop2cnf(p->prop.Binary_prop.prop2, data);
      res = ++(data->prop_cnt);
      clause_gen_binary(p1, p2, res, p->prop.Binary_prop.op, data);
      break;
    }
    case SMTU_PROP: {
      int p1 = prop2cnf(p->prop.Unary_prop.prop1, data);
      res = ++(data->prop_cnt);
      clause_gen_unary(p1, res, data);
      break;
    }
    case SMT_PROPVAR:
      res = p->prop.Propvar;
      break;
    default:
      // unreachable
  }
  return res;
}