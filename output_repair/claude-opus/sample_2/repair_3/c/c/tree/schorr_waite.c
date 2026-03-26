#include <stdbool.h>

struct node
{
  bool m;
  bool c;
  struct node *l;
  struct node *r;
};

/*@ predicate node(struct node *n;) = 
      n->m |-> _ &*& n->c |-> _ &*& n->l |-> _ &*& n->r |-> _; @*/

/*@ predicate tree(struct node *n;) = 
      n == 0 ? emp : node(n) &*& tree(n->l) &*& tree(n->r); @*/

/*@ predicate stack(struct node *p;) =
      p == 0 ? emp : node(p) &*& stack(p->l) &*& stack(p->r); @*/

void schorr_waite(struct node *root)
//@ requires tree(root);
//@ ensures true;
{
  struct node *t = root;
  struct node *p = 0;
  //@ open tree(root);

  while (p != 0 || (t != 0 && !(t->m)))
  //@ invariant stack(p) &*& tree(t);
  {
    if (t == 0 || t->m)
    {
      //@ open stack(p);
      if (p->c)
      {
        struct node *q = t;
        t = p;
        //@ close tree(q);
        p = p->r;
        t->r = q;
        //@ close stack(p);
        //@ open tree(t);
      }
      else
      {
        struct node *q = t;
        t = p->r;
        p->r = p->l;
        p->l = q;
        p->c = true;
        //@ close stack(p);
      }
    }
    else
    {
      //@ open tree(t);
      struct node *q = p;
      p = t;
      t = t->l;
      p->l = q;
      p->m = true;
      p->c = false;
      //@ close stack(p);
    }
  }//@ close tree(t);
}