struct node {
  bool m; 
  bool c; 
  struct node* l;
  struct node* r;
  
};

/*@ 
predicate node(struct node* n; 
               bool m, bool c, 
               struct node* l, struct node* r) = 
    n->m |-> m &*& 
    n->c |-> c &*& 
    n->l |-> l &*& 
    n->r |-> r;
@*/

/*@
predicate graph(struct node* n) = 
    n == 0 ? true : 
    node(n, _, _, _, _) &*&
    // We do not unfold l and r here to avoid infinite recursion.
    true;
@*/

void schorr_waite(struct node* root) 
  //@ requires graph(root);
  //@ ensures graph(root);
  
{
  struct node* t = root; 
  struct node* p = 0;
  //@ open graph(root);
  
  while(p != 0 || (t != 0 && !(t->m))) //@
    //@ requires graph(t) &*& graph(p);
    //@ ensures graph(t) &*& graph(p);
  {
    if(t == 0 || t->m) {
      
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
    } else { 
      struct node* q = p;
      p = t;
      t = t->l;
      p->l = q;
      p->m = true;
      p->c = false;
      
    }
  }
  //@ close graph(root);
}