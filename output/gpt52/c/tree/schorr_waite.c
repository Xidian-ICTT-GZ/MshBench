#include <stdbool.h>

struct node
{
  bool m;
  bool c;
  struct node *l;
  struct node *r;
};

/*@

predicate node_fields(struct node *n; bool m, bool c, struct node *l, struct node *r) =
  n->m |-> m &*& n->c |-> c &*& n->l |-> l &*& n->r |-> r;

@*/

void schorr_waite(struct node *root)
  //@ requires root == 0 ? true : node_fields(root, ?m, ?c, ?l, ?r);
  //@ ensures root == 0 ? true : node_fields(root, ?m2, ?c2, ?l2, ?r2);
{
  struct node *t = root;
  struct node *p = 0;

  while (p != 0 || (t != 0 && !(t->m)))
  //@ invariant (p == 0 ? true : node_fields(p, ?pm, ?pc, ?pl, ?pr)) &*& (t == 0 ? true : node_fields(t, ?tm, ?tc, ?tl, ?tr));
  {
    if (t == 0 || t->m)
    {
      //@ if (p != 0) open node_fields(p, ?pm, ?pc, ?pl, ?pr);
      if (p->c)
      {
        //@ open node_fields(p, pm, pc, pl, pr);
        //@ if (t != 0) open node_fields(t, ?tm, ?tc, ?tl, ?tr);
        struct node *q = t;
        t = p;
        p = p->r;
        t->r = q;
        //@ close node_fields(t, pm, pc, pl, q);
        //@ if (p != 0) close node_fields(p, ?pm2, ?pc2, ?pl2, ?pr2);
      }
      else
      {
        //@ open node_fields(p, pm, pc, pl, pr);
        //@ if (t != 0) open node_fields(t, ?tm, ?tc, ?tl, ?tr);
        struct node *q = t;
        t = p->r;
        p->r = p->l;
        p->l = q;
        p->c = true;
        //@ close node_fields(p, pm, true, q, pl);
        //@ if (t != 0) close node_fields(t, ?tm2, ?tc2, ?tl2, ?tr2);
      }
      //@ if (p != 0) close node_fields(p, ?pm3, ?pc3, ?pl3, ?pr3);
    }
    else
    {
      //@ open node_fields(t, ?tm, ?tc, ?tl, ?tr);
      struct node *q = p;
      p = t;
      t = t->l;
      p->l = q;
      p->m = true;
      p->c = false;
      //@ close node_fields(p, true, false, q, tr);
      //@ if (t != 0) close node_fields(t, ?tm2, ?tc2, ?tl2, ?tr2);
    }
  }
}