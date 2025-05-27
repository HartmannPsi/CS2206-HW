#include "ast.h"

term *subst_var(char *den, char *src, term *t)
/*@ With term src_str den_str
      Require store_term(t, term) *
              store_string(src, src_str) *
              store_string(den, den_str)
      Ensure __return == t && t == t@pre && den == den@pre && src == src@pre &&
             store_term(t, term_subst_v(den, src, term)) *
             store_string(den, den_str) *
             store_string(src, src_str)
*/
{
  switch (t->type) {
    case Var: {
      if (!strcmp(t->content.Var, src)) {
        free_str(t->content.Var);
        t->content.Var = strdup(den);
      }
      break;
    }
    case Const: {
      break;
    }
    case Apply: {
      t->content.Apply.left = subst_var(den, src, t->content.Apply.left);
      t->content.Apply.right = subst_var(den, src, t->content.Apply.right);
      break;
    }
    case Quant: {
      if (strcmp(t->content.Quant.var, src)) {
        t->content.Quant.body = subst_var(den, src, t->content.Quant.body);
      }
      break;
    }
    default: {
      break;
    }
  }
  return t;
}

term *subst_term(term *den, char *src, term *t)
/*@ With term src_str den_term
      Require store_term(t, term) *
              store_string(src, src_str) *
              store_term(den, den_term)
      Ensure __return == t && t == t@pre && den == den@pre && src == src@pre &&
             store_term(t, term_subst_t(den, src, term)) *
             store_term(den, den_term) *
             store_string(src, src_str)
*/{
  switch (t->type) {
    case Var: {
      if (!strcmp(t->content.Var, src)) {
        free_term(t);
        t = copy_term(den);
      }
      break;
    }
    case Const: {
      break;
    }
    case Apply: {
      t->content.Apply.left = subst_term(den, src, t->content.Apply.left);
      t->content.Apply.right = subst_term(den, src, t->content.Apply.right);
      break;
    }
    case Quant: {
      if (strcmp(t->content.Quant.var, src)) {
        t->content.Quant.body = subst_term(den, src, t->content.Quant.body);
      }
      break;
    }
    default: {
      break;
    }
  }
  return t;
}