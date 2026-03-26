struct list_node {
  int value;
  struct list_node* next;
};

/*@
predicate list(struct list_node* n) =
  n == 0 ?
    true
  :
    n->value |-> ?v &*& n->next |-> ?nx &*& list(nx);

predicate lseg(struct list_node* from, struct list_node* to) =
  from == to ?
    true
  :
    from->value |-> ?v &*& from->next |-> ?nx &*& lseg(nx, to);
@*/

static int compare(struct list_node* n0, struct list_node* n1)
//@ requires n0->value |-> ?v0 &*& n1->value |-> ?v1;
//@ ensures n0->value |-> v0 &*& n1->value |-> v1;
{
  if (n0->value < n1->value) {
    return -1;
  } else if (n0->value > n1->value) {
    return 1;
  } else {
    return 0;
  }
}

void insertion_sort_core(struct list_node** pfirst)
//@ requires pfirst |-> ?f &*& list(f);
//@ ensures pfirst |-> ?f2 &*& list(f2);
{
  if (*pfirst == 0) {
    
    return;
  }  
  
  struct list_node* last_sorted = *pfirst;
  while (last_sorted->next != 0)
    //@ invariant pfirst |-> ?f0 &*& lseg(f0, last_sorted) &*& last_sorted->value |-> ?lv &*& last_sorted->next |-> ?ln &*& list(ln);
  {
    //@ open list(ln);
    
    
    
    struct list_node** pn = pfirst;
    
    int comparison = compare(*pn, last_sorted->next); 
    
    while (pn != &(last_sorted->next) && comparison < 0)
      //@ invariant pfirst |-> f0 &*& last_sorted->value |-> lv &*& last_sorted->next |-> ln &*& lseg(f0, last_sorted) &*& lseg(f0, pn) &*& *pn |-> ?cur &*& list(cur) &*& cur != 0 &*& cur->value |-> ?cv &*& cur->next |-> ?cn &*& lseg(cn, last_sorted) &*& list(ln);
    { 
      //@ open list(cur);
      //@ close lseg(f0, pn);
      pn = &((*pn)->next);
      
      
      
      
      
      if (pn != &(last_sorted->next)) {
        
        //@ open list(cn);
        comparison = compare(*pn, last_sorted->next);
        //@ close list(cn);
      } else {
      }
      //@ close list(cur);
    }
    
    
    
    
    

    if (pn != &(last_sorted->next)) {
      struct list_node* first_unsorted = last_sorted->next;
      
      
      last_sorted->next = first_unsorted->next;
      
      first_unsorted->next = *pn;
      *pn = first_unsorted;
      
      

      
    } else {
      
      
      last_sorted = last_sorted->next;
      
      
      
    }
    //@ close list(ln);
  }
  
  
  
  
}

struct list_node* insertion_sort(struct list_node* l)
//@ requires list(l);
//@ ensures list(result);
{
  insertion_sort_core(&l);
  return l;
}