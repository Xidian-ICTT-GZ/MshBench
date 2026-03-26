#include <stdbool.h>

struct node {
  bool m; 
  bool c; 
  struct node* l;
  struct node* r;
  
};

/*@

predicate node_fields(struct node *n; bool m, bool c, struct node *l, struct node *r) =
  n->m |-> m &*& n->c |-> c &*& n->l |-> l &*& n->r |-> r;

predicate schorr_state(struct node *t, struct node *p) =
  t == 0 ?
    true
  :
    node_fields(t; ?tm, ?tc, ?tl, ?tr) &*& schorr_state(tl, p) &*& schorr_state(tr, p);

@*/

void schorr_waite(struct node* root) 
  //@ requires true;
  //@ ensures true;
  
  
{
  struct node* t = root; 
  struct node* p = 0;
  
  
  while(p != 0 || (t != 0 && ! (t->m)))
    //@ invariant true;
    
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
  
  
}