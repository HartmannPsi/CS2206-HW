#include "ast.h"

term* sub_thm(term* thm, var_sub_list* list)
/*@ With t l
      Require store_term(thm, t) * sll_var_sub_list(list, l)
      Ensure thm == thm@pre && list == list@pre &&
              sll_var_sub_list(list, l) *
              store_term_res(__return, thm_subst(t, l))
*/
{
  if(list == (void*) 0) return thm;
  /*@ store_term(thm, t)
      which implies
        thm != 0
  */
  if(thm->type == Quant && thm->content.Quant.type == Forall){
      term* den = list->cur->sub_term;
      if (strcmp(thm->content.Quant.var, list->cur->var))
          return (void*) 0; //变量名不匹配
      return sub_thm(subst_term(den, list->cur->var, thm->content.Quant.body), list->next);
  }
  else return (void*) 0;
}

// apply (apply (impl) h1) (h2)
// 不是imply形式时返回(void*) 0
ImplyProp* separate_imply(term* t) 
/*@ With trm
    Require store_term(t, trm)
    Ensure t == t@pre && store_imply_res(__return, sep_impl(trm))
*/
{
  if (t->type != Apply || t->content.Apply.left->type != Apply ||
      t->content.Apply.left->content.Apply.left->type != Const ||
      t->content.Apply.left->content.Apply.left->content.Const.type != Impl)
    return (void*)0;
  else
    return createImplyProp(t->content.Apply.left->content.Apply.right,
                           t->content.Apply.right);
}

// 根据定理形式，匹配结论，得出要检验的前提
term_list* check_list_gen(term* thm, term* target)
/*@ With theo targ
    Require store_term(thm, theo) * store_term(target, targ)
    Ensure target == target@pre &&
            store_term(thm@pre, theo) * store_term(target, targ) *
            sll_term_list(__return, gen_pre(theo, targ))
*/
{
  if (thm == (void*)0 || target == (void*)0) {
    return (void*)0;
  }
  term_list* check_list = (void*)0;
  term_list** tail_ptr = &check_list;
  while (thm != (void*)0 && !alpha_equiv(thm, target)) {
    ImplyProp* p = separate_imply(thm);
    if (p == (void*)0) {
      free_term_list(check_list);
      return (void*)0;
    }
    // 添加新节点到链表
    term_list* new_node = malloc_term_list();
    new_node->element = p->assum;  // 转移所有权
    new_node->next = (void*)0;

    *tail_ptr = new_node;
    tail_ptr = &(new_node->next);
    thm = p->concl;
    free_imply_prop(p);  // 释放ImplyProp结构体（不释放其成员）
  }
  return check_list;
}

solve_res* thm_apply(term* thm, var_sub_list* list, term* goal) 
/*@ With t l g
    Require store_term(thm, t) * 
            sll_var_sub_list(list, l) * 
            store_term(goal, g)
    Ensure thm == thm@pre && 
            sll_var_sub_list(list, l) * 
            store_term(goal, g) *
            store_solve_res(__return, thm_app(t, l, g))
*/
{
  term* thm_ins = sub_thm(thm, list);
  solve_res* res = malloc_solve_res();
  if (thm_ins == (void*)0) {
    res->type = bool_res;
    res->d.ans = 0;
  } else if (alpha_equiv(thm_ins, goal)) {
    res->type = bool_res;
    res->d.ans = 1;
  } else {
    res->type = termlist;
    res->d.list = check_list_gen(thm_ins, goal);
  }
  return res;
}