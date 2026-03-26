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
@*/

void schorr_waite(struct node *root)
//@ requires node(root, ?mr, ?cr, ?lr, ?rr);
//@ ensures node(root, true, cr, lr, rr);
{
  struct node *t = root;
  struct node *p = 0;
  //@ close node(root, mr, cr, lr, rr);
  //@ struct node *ot = t; struct node *op = p;
  //@ bool ot_m = mr; bool ot_c = cr; struct node *ot_l = lr; struct node *ot_r = rr;

  while (p != 0 || (t != 0 && !(t->m)))
  //@ invariant (p == 0 ? true : node(p, ?pm, ?pc, ?pl, ?pr)) &*& (t == 0 ? true : node(t, ?tm, ?tc, ?tl, ?tr)) &*& (p == 0 && t == 0 ? true : p != 0 || t != 0);
  {
    //@ open (p == 0 ? true : node(p, pm, pc, pl, pr));
    //@ open (t == 0 ? true : node(t, tm, tc, tl, tr));
    if (t == 0 || t->m)
    {
      //@ assert p != 0;
      //@ open node(p, pm, pc, pl, pr);
      if (p->c)
      {
        struct node *q = t;
        t = p;
        p = p->r;
        t->r = q;
        //@ close node(t, pm, pc, pl, q);
        //@ ot = t; op = p; ot_m = pm; ot_c = pc; ot_l = pl; ot_r = q;
      }
      else
      {
        struct node *q = t;
        t = p->r;
        p->r = p->l;
        p->l = q;
        p->c = true;
        //@ close node(p, pm, true, q, pl);
        //@ ot = t; op = p; ot_m = pm; ot_c = true; ot_l = q; ot_r = pl;
      }
    }
    else
    {
      //@ assert t != 0;
      //@ open node(t, tm, tc, tl, tr);
      struct node *q = p;
      p = t;
      t = t->l;
      p->l = q;
      p->m = true;
      p->c = false;
      //@ close node(p, true, false, q, tr);
      //@ ot = t; op = p; ot_m = true; ot_c = false; ot_l = q; ot_r = tr;
    }
    //@ close (op == 0 ? true : node(op, ot_m, ot_c, ot_l, ot_r));
    //@ close (ot == 0 ? true : node(ot, ?ntm, ?ntc, ?ntl, ?ntr));
  }
  //@ open (p == 0 ? true : node(p, pm, pc, pl, pr));
  //@ open (t == 0 ? true : node(t, tm, tc, tl, tr));
  //@ close node(root, true, cr, lr, rr);
}