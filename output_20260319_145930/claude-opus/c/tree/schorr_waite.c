struct node {
  bool m; 
  bool c; 
  struct node* l;
  struct node* r;
  
};

/*@
predicate node(struct node* n;) =
  n->m |-> _ &*& n->c |-> _ &*& n->l |-> _ &*& n->r |-> _;

predicate tree(struct node* t;) =
  t == 0 ? true : node(t) &*& tree(t->l) &*& tree(t->r);

predicate stack(struct node* p;) =
  p == 0 ? true :
    node(p) &*& 
    (p->c ? tree(p->l) &*& stack(p->r) : stack(p->l) &*& tree(p->r));

predicate graph(struct node* t, struct node* p;) =
  stack(p) &*& tree(t);
@*/

void schorr_waite(struct node* root) 
//@ requires tree(root);
//@ ensures tree(root);
{
  struct node* t = root; 
  struct node* p = 0;
  //@ close stack(0);
  
  while(p != 0 || (t != 0 && ! (t->m)))
    //@ invariant graph(t, p);
  {
    if(t == 0 || t->m) {
      //@ open stack(p);
      if(p->c) { 
        struct node* q = t;
        t = p;
        p = p->r;
        //@ open node(t);
        t->r = q;
        //@ close tree(t);
        
      } else { 
        struct node* q = t;
        //@ open node(p);
        t = p->r;
        p->r = p->l;
        p->l = q;
        p->c = true;
        //@ close node(p);
        //@ close stack(p);
        
        
      }
    } else { 
      //@ open tree(t);
      struct node* q = p;
      p = t;
      //@ open node(p);
      t = t->l;
      p->l = q;
      p->m = true;
      p->c = false;
      //@ close node(p);
      //@ close stack(p);
      
      
    }
  }
  //@ open stack(p);
  
  
}