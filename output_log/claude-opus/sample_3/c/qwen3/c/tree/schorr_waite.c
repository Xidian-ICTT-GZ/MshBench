/*@
predicate tree(struct node *root; bool marked) =
  root == 0 ? emp :
  root->m |-> marked &*&
  root->c |-> _ &*&
  root->l |-> ?l &*&
  root->r |-> ?r &*&
  tree(l, marked) &*&
  tree(r, marked);
@*/

/*@ 
predicate schorr_waite_state(struct node *t, struct node *p; struct node *root) =
  t == 0 &*& p == 0 ? tree(root, true) :
  t != 0 &*& p == 0 ? tree(t, false) &*& tree(root, true) :
  t == 0 &*& p != 0 ? tree(p, false) &*& tree(root, true) :
  t != 0 &*& p != 0 ?
    p->c |-> ?c &*&
    tree(p->l, false) &*& tree(p->r, false) &*& tree(t, false) &*&
    ((p->l == 0 || (p->l->m == false)) &*& (p->r == 0 || (p->r->m == false))) 
  : false;
@*/

void schorr_waite(struct node *root)
//@ requires tree(root, false);
//@ ensures tree(root, true);
{
  struct node *t = root;
  struct node *p = 0;

  //@ invariant schorr_waite_state(t, p, root);
  while (p != 0 || (t != 0 && !(t->m)))
  /*@ invariant schorr_waite_state(t, p, root); @*/
  {
    //@ assert schorr_waite_state(t, p, root);
    if (t == 0 || t->m)
    {
      //@ assert p != 0;
      if (p->c)
      {
        struct node *q = t;
        //@ assert p->c == true;
        //@ assert tree(p->l, false) &*& tree(p->r, false) &*& tree(t, false);
        //@ assert p->r == 0 || p->r->m == false;
        t = p;
        p = p->r;
        t->r = q;
        //@ assert schorr_waite_state(t, p, root);
      }
      else
      {
        struct node *q = t;
        //@ assert p->c == false;
        //@ assert tree(p->l, false) &*& tree(p->r, false) &*& tree(t, false);
        t = p->r;
        p->r = p->l;
        p->l = q;
        p->c = true;
        //@ assert schorr_waite_state(t, p, root);
      }
    }
    else
    {
      struct node *q = p;
      //@ assert t != 0 && t->m == false;
      //@ assert tree(t, false) &*& tree(root, true);
      p = t;
      t = t->l;
      p->l = q;
      p->m = true;
      p->c = false;
      //@ assert schorr_waite_state(t, p, root);
    }
  }
  //@ assert t == 0 && p == 0;
  //@ assert tree(root, true);
}