#include <stdbool.h>

struct node
{
  bool m;
  bool c;
  struct node *l;
  struct node *r;
};

/*@ predicate node(struct node *n) = n->m |-> _ &*& n->c |-> _ &*& n->l |-> _ &*& n->r |-> _; @*/

/*@ predicate tree(struct node *n) = 
  n == 0 ? true : (node(n) &*& tree(n->l) &*& tree(n->r)); 
@*/

void schorr_waite(struct node *root)
//@ requires tree(root);
//@ ensures tree(root);
{
  struct node *t = root;
  struct node *p = 0;

  //@ invariant (p == 0 || node(p)) &*& (t == 0 || node(t));
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