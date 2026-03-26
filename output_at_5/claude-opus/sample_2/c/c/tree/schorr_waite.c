struct node {
  bool m; 
  bool c; 
  struct node* l;
  struct node* r;
  
};

/*@
predicate nodes(struct node* n) =
  n == 0 ? true :
  malloc_block_node(n) &*& 
  (n->m == true || n->m == false) &*&
  (n->c == true || n->c == false) &*&
  nodes(n->l) &*& nodes(n->r);
@*/

void schorr_waite(struct node* root) 
  //@ requires nodes(root);
  //@ ensures nodes(root);
{
  struct node* t = root; 
  struct node* p = 0;
  
  //@ open nodes(root);
  while(p != 0 || (t != 0 && ! (t->m)))
    //@ requires nodes(t) &*& nodes(p);
    //@ ensures nodes(t) &*& nodes(p);
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
  //@ close nodes(root);
}