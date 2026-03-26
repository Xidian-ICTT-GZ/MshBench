struct node
{
  bool m;
  bool c;
  struct node *l;
  struct node *r;
};

/*@
predicate node(struct node *n;) =
  n->m |-> _ &*& n->c |-> _ &*& n->l |-> _ &*& n->r |-> _;

predicate tree(struct node *n;) =
  n == 0 ?
    emp
  :
    n->m |-> _ &*& n->c |-> _ &*& n->l |-> ?l &*& n->r |-> ?r &*& tree(l) &*& tree(r);

predicate stack(struct node *p;) =
  p == 0 ?
    emp
  :
    p->m |-> _ &*& p->c |-> ?c &*& p->l |-> ?l &*& p->r |-> ?r &*&(c == false ? stack(l) &*& tree(r) : stack(r) &*& tree(l));
@*/

void schorr_waite(struct node *root)
//@ requires tree(root);
//@ ensures true;
{
  struct node *t = root;
  struct node *p = 0;

  //@ open tree(root);
  //@ close stack(0);
  while (p != 0 || (t != 0 && !(t->m)))
  //@ invariant tree(t) &*& stack(p);
  {
    if (t == 0 || t->m)
    {
      //@ open stack(p);
      if (p->c)
      {
        struct node *q = t;
        t = p;
        p = p->r;
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
  }//@ open stack(p);
  //@ close tree(t);
}