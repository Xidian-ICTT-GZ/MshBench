#include <stdbool.h>

struct node {
  struct node *l;
  struct node *r;
  bool m;
  bool c;
};

/*@ predicate tree(struct node *root; bool marked) =
    root == 0 ?
      emp
    :
      root->l |-> ?l &*& root->r |-> ?r &*& root->m |-> marked &*& root->c |-> _ &*&
      tree(l, marked) &*& tree(r, marked);
@*/

/*@ predicate stack(struct node *p, struct node *root; list<struct node*> nodes) =
    p == 0 ?
      nodes == nil
    :
      p->l |-> ?l &*& p->r |-> ?r &*& p->m |-> true &*& p->c |-> ?c &*&
      (c == false ?
        tree(r, false) &*& stack(l, root, ?rest) &*& nodes == cons(p, rest)
      :
        tree(l, true) &*& stack(r, root, ?rest) &*& nodes == cons(p, rest));
@*/

void schorr_waite(struct node *root)
//@ requires tree(root, false);
//@ ensures tree(root, true);
{
  struct node *t = root;
  struct node *p = 0;
  //@ close stack(0, root, nil);

  while (p != 0 || (t != 0 && !(t->m)))
  //@ invariant tree(t, false) &*& stack(p, root, ?nodes);
  {
    if (t == 0 || t->m)
    {
      //@ open stack(p, root, nodes);
      if (p->c)
      {
        struct node *q = t;
        t = p;
        p = p->r;
        t->r = q;
        //@ close tree(t, true);
      }
      else
      {
        struct node *q = t;
        t = p->r;
        p->r = p->l;
        p->l = q;
        p->c = true;
        //@ close stack(p, root, nodes);
      }
    }
    else
    {
      //@ open tree(t, false);
      struct node *q = p;
      p = t;
      t = t->l;
      p->l = q;
      p->m = true;
      p->c = false;
      //@ close stack(p, root, cons(p, nodes));
    }
  }
  //@ open stack(0, root, _);
  //@ close tree(0, true);
}