/*@ predicate nodeseg(struct node* p; struct node* end) =
    p == end ?
      true
    :
      p != 0 &*& malloc_block_node(p) &*& nodeseg(p->l, end) &*& nodeseg(p->r, end);
@*/

void schorr_waite(struct node* root)
//@ requires nodeseg(root, 0);
//@ ensures true;
{
  struct node* t = root;
  struct node* p = 0;

  while(p != 0 || (t != 0 && ! (t->m)))
    //@ invariant nodeseg(t, 0) &*& nodeseg(p, 0);
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