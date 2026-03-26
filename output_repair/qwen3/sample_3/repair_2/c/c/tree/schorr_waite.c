#include <stdbool.h>

struct node
{
  bool m;
  bool c;
  struct node *l;
  struct node *r;
};

/*@ predicate node(struct node *n; bool m_val, bool c_val, struct node *l_val, struct node *r_val) =
  n != 0 &*&
  n->m |-> m_val &*&
  n->c |-> c_val &*&
  n->l |-> l_val &*&
  n->r |-> r_val;
@*/

/*@ predicate tree(struct node *n) =
  n == 0 ?
    true
  :
    exists(?m_val, ?c_val, ?l_val, ?r_val) &*&
    node(n, m_val, c_val, l_val, r_val) &*&
    tree(l_val) &*&
    tree(r_val);
@*/

void schorr_waite(struct node *root)
//@ requires tree(root);
//@ ensures tree(root);
{
  struct node *t = root;
  struct node *p = 0;

  //@ invariant (p == 0 || exists(?pm, ?pc, ?pl, ?pr) &*& node(p, pm, pc, pl, pr)) &*& (t == 0 || exists(?tm, ?tc, ?tl, ?tr) &*& node(t, tm, tc, tl, tr));
  while (p != 0 || (t != 0 && !(t->m)))
  {
    if (t == 0 || t->m)
    {
      if (p->c)
      {
        struct node *q = t;
        t = p;
        p = p->r;
        t->r = q;
      }
      else
      {
        struct node *q = t;
        t = p->r;
        p->r = p->l;
        p->l = q;
        p->c = true;
      }
    }
    else
    {
      struct node *q = p;
      p = t;
      t = t->l;
      p->l = q;
      p->m = true;
      p->c = false;
    }
  }
}