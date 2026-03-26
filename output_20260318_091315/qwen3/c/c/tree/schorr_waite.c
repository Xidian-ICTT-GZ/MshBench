/*@ predicate tree(struct node* n; struct node* parent) =
  n == 0 ?
    true
  :
    malloc_block_node(n) &*&
    tree(n->l, n) &*&
    tree(n->r, n);
@*/

/*@ predicate schorr_waite_space(struct node* n) =
  n == 0 ?
    true
  :
    malloc_block_node(n) &*&
    schorr_waite_space(n->l) &*&
    schorr_waite_space(n->r);
@*/

void schorr_waite(struct node* root)
//@ requires schorr_waite_space(root);
//@ ensures schorr_waite_space(root);
{
  struct node* t = root; 
  struct node* p = 0;
  
  //@ open schorr_waite_space(root);
  
  while(p != 0 || (t != 0 && ! (t->m)))
    //@ invariant schorr_waite_space(t) &*& schorr_waite_space(p) &*& (p != 0 || t != 0);
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