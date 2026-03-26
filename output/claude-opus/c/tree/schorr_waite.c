struct node
{
  bool m;
  bool c;
  struct node *l;
  struct node *r;
};

/*@
predicate node(struct node *n; bool m, bool c, struct node *l, struct node *r) =
  n->m |-> m &*& n->c |-> c &*& n->l |-> l &*& n->r |-> r;

predicate lseg(struct node *from, struct node *to) =
  from == to ? emp : node(from, _, _, _, ?next) &*& lseg(next, to);

predicate tree(struct node *t) =
  t == 0 ? emp : node(t, _, _, ?l, ?r) &*& tree(l) &*& tree(r);

predicate stack(struct node *p) =
  p == 0 ? emp : node(p, true, ?c, ?l, ?r) &*& 
    (c == false ? tree(r) &*& stack(l) : stack(r));

predicate sw_state(struct node *t, struct node *p, struct node *root) =
  stack(p) &*& 
  (t == 0 ? emp : (p == 0 || t->m == false ? tree(t) : node(t, _, _, ?l, ?r) &*& tree(l) &*& tree(r)));
@*/

void schorr_waite(struct node *root)
//@ requires tree(root);
//@ ensures tree(root);
{
  struct node *t = root;
  struct node *p = 0;

  while (p != 0 || (t != 0 && !(t->m)))
  //@ invariant p == 0 &*& t == 0 ? emp : p == 0 ? tree(t) : stack(p) &*& tree(t);
  {
    //@ open tree(t);
    if (t == 0 || t->m)
    {
      //@ open stack(p);
      if (p->c)
      {
        struct node *q = t;
        t = p;
        p = p->r;
        t->r = q;
        //@ close tree(t);
      }
      else
      {
        struct node *q = t;
        t = p->r;
        p->r = p->l;
        p->l = q;
        p->c = true;
        //@ close stack(p);
        //@ close tree(t);
      }
    }
    else
    {
      //@ open node(t, _, _, ?tl, ?tr);
      struct node *q = p;
      p = t;
      t = t->l;
      p->l = q;
      p->m = true;
      p->c = false;
      //@ close node(p, true, false, q, tr);
      //@ close stack(p);
    }
  }
  //@ close tree(t);
}