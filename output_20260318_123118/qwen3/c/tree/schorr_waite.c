/*@ predicate tree(struct node* n; struct node* parent) =
    n == 0 ?
        true
    :
        malloc_block_node(n) &*&
        tree(n->l, n) &*&
        tree(n->r, n) &*&
        n->m == false &*&
        n->c == false;
@*/

/*@ predicate marked_tree(struct node* n; struct node* parent) =
    n == 0 ?
        true
    :
        malloc_block_node(n) &*&
        (n->m ?
            (n->c ?
                marked_tree(n->r, n) &*&
                marked_tree(n->l, n)
            :
                marked_tree(n->l, n) &*&
                tree(n->r, n)
            )
        :
            false
        );
@*/

void schorr_waite(struct node* root)
//@ requires tree(root, 0);
//@ ensures marked_tree(root, 0);
{
  struct node* t = root; 
  struct node* p = 0;
  
  //@ invariant
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
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