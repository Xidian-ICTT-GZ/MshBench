struct node {
  bool m; 
  bool c; 
  struct node* l;
  struct node* r;
  
};

/*@

predicate node_fields(struct node *n) =
  n->m |-> _ &*&
  n->c |-> _ &*&
  n->l |-> _ &*&
  n->r |-> _;

@*/

void schorr_waite(struct node* root) 
  //@ requires true;
  //@ ensures true;
  
  
{
  struct node* t = root; 
  struct node* p = 0;
  
  
  while(p != 0 || (t != 0 && ! (t->m)))
    //@ invariant p == 0 ? true : node_fields(p);
    
  {
    //@ if (t != 0) { assume(node_fields(t)); }
    if(t == 0 || t->m) {
      
      //@ assume(p != 0);
      //@ open node_fields(p);
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
      //@ close node_fields(t);
    } else { 
      struct node* q = p;
      p = t;
      t = t->l;
      //@ open node_fields(p);
      p->l = q;
      p->m = true;
      p->c = false;
      //@ close node_fields(p);
      
      
    }
  }
  
  
}