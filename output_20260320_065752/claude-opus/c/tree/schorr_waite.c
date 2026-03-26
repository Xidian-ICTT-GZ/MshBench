struct node {
  bool m; 
  bool c; 
  struct node* l;
  struct node* r;
  
};

/*@ predicate nodep(struct node* n) =
      n == 0 ? true :
      malloc_block_node(n) &*&
      n->m |-> ?m &*&
      n->c |-> ?c &*&
      n->l |-> ?l &*& nodep(l) &*&
      n->r |-> ?r &*& nodep(r);
@*/

typedef struct node node;

//@ requires nodep(root);
//@ ensures nodep(root);
void schorr_waite(struct node* root) 
  
  
{
  struct node* t = root; 
  struct node* p = 0;
  
  //@ open nodep(root);

  //@ predicate inv(struct node* t, struct node* p) = 
  //@    nodep(t) &*& nodep(p);
  
  while(p != 0 || (t != 0 && !(t->m))) 
    //@ invariant nodep(t) &*& nodep(p);
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
  
  //@ close nodep(root);
}