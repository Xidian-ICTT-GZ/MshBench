struct node {
  bool m; 
  bool c; 
  struct node* l;
  struct node* r;
  
};

/*@

predicate node(struct node *n) =
  n == 0 ?
    true
  :
    n->m |-> _ &*&
    n->c |-> _ &*&
    n->l |-> _ &*&
    n->r |-> _;

@*/

void schorr_waite(struct node* root) 
  //@ requires node(root);
  //@ ensures node(root);
  
  
{
  struct node* t = root; 
  struct node* p = 0;
  
  
  while(p != 0 || (t != 0 && ! (t->m)))
    //@ invariant node(p) &*& node(t);
    
  {
    //@ open node(t);
    if(t == 0 || t->m) {
      
      //@ open node(p);
      if(p->c) { 
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
      //@ close node(p);
      //@ close node(t);
    } else { 
      struct node* q = p;
      p = t;
      t = t->l;
      p->l = q;
      p->m = true;
      p->c = false;
      
      //@ close node(p);
      //@ close node(t);
      
      
    }
  }
  
  
}