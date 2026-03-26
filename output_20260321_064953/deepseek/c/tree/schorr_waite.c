struct node {
  bool m; 
  bool c; 
  struct node* l;
  struct node* r;
  
};

/*@
predicate node(struct node* n; bool m, bool c, struct node* l, struct node* r) =
  n->m |-> m &*& n->c |-> c &*& n->l |-> l &*& n->r |-> r &*& malloc_block_node(n);
@*/

void schorr_waite(struct node* root) 
  //@ requires node(root, ?m0, ?c0, ?l0, ?r0);
  //@ ensures node(root, _, _, _, _);
  
{
  struct node* t = root; 
  struct node* p = 0;
  //@ close node(root, m0, c0, l0, r0);
  //@ struct node* ot = t; struct node* op = p;
  
  while(p != 0 || (t != 0 && ! (t->m)))
    //@ invariant (p == 0 ? true : node(p, ?pm, ?pc, ?pl, ?pr)) &*& (t == 0 ? true : node(t, ?tm, ?tc, ?tl, ?tr));
    
  {
    if(t == 0 || t->m) {
      //@ open node(p, pm, pc, pl, pr);
      
      if(p->c) { 
        struct node* q = t;
        t = p;
        p = p->r;
        t->r = q;
        //@ close node(t, pm, pc, pl, q);
        
      } else { 
        struct node* q = t;
        t = p->r;
        p->r = p->l;
        p->l = q;
        p->c = true;
        //@ close node(p, pm, true, q, pl);
        
        
        
      }
    } else { 
      //@ open node(t, tm, tc, tl, tr);
      struct node* q = p;
      p = t;
      t = t->l;
      p->l = q;
      p->m = true;
      p->c = false;
      //@ close node(p, true, false, q, tr);
      
      
    }
  }
  //@ open node(t, _, _, _, _);
  //@ open node(p, _, _, _, _);
  
  
}