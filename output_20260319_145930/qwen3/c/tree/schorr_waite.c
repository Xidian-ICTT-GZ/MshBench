/*@ predicate tree(struct node* root; ) = 
    root == 0 ? 
        true 
    : 
        malloc_block_node(root) &*& 
        tree(root->l) &*& 
        tree(root->r); 
@*/

void schorr_waite(struct node* root)
//@ requires tree(root);
//@ ensures tree(root);
{
  struct node* t = root; 
  struct node* p = 0;
  
  //@ open tree(root);
  //@ if (root != 0) { close tree(root); }
  
  while(p != 0 || (t != 0 && ! (t->m)))
    //@ invariant p == 0 ? true : (malloc_block_node(p) &*& p->m == true);
    //@ invariant t == 0 ? true : (malloc_block_node(t) &*& tree(t->l) &*& tree(t->r));
    //@ invariant p != 0 || t != 0;
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