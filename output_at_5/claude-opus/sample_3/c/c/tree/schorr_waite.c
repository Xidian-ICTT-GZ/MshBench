struct node {
  bool m; 
  bool c; 
  struct node* l;
  struct node* r;
  
};

/*@
predicate node(struct node* n; bool m, bool c, struct node* l, struct node* r) =
  n != 0 &*&
  malloc_block_node(n) &*&
  n->m |-> m &*& n->c |-> c &*& n->l |-> l &*& n->r |-> r;
@*/

void schorr_waite(struct node* root) 
  //@ requires root == 0 ? true : node(root, ?m, ?c, ?l, ?r);
  //@ ensures true;
{
  struct node* t = root; 
  struct node* p = 0;
  
  //@ open node(root, _, _, _, _);
  while(p != 0 || (t != 0 && !(t->m)))
    //@ requires (t == 0 ? true : node(t, ?tm, ?tc, ?tl, ?tr)) &*& (p == 0 ? true : node(p, ?pm, ?pc, ?pl, ?pr));
    //@ ensures  (t == 0 ? true : node(t, ?tm2, ?tc2, ?tl2, ?tr2)) &*& (p == 0 ? true : node(p, ?pm2, ?pc2, ?pl2, ?pr2));
  {
    if(t == 0 || t->m) {
      if (p->c) {
        struct node* q = t;
        t = p;
        p = p->r;
        t->r = q;
      } else {
        struct node* q = t;
        t = p->r;
        p->r = p->l;
        p->l = q;
        p->c = true;
      }
    } else {
      struct node* q = p;
      p = t;
      t = t->l;
      p->l = q;
      p->m = true;
      p->c = false;
    }
  }
  //@ close node(root, _, _, _, _);
}