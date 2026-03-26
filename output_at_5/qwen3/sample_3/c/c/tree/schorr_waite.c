#include <stdbool.h>

struct node {
  bool m; 
  bool c; 
  struct node* l;
  struct node* r;
};

//@ requires true;
//@ ensures true;
void schorr_waite(struct node* root) 
{
  struct node* t = root; 
  struct node* p = 0;
  
  while(p != 0 || (t != 0 && ! (t->m)))
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