struct list_node {
  int value;
  struct list_node* next;
};

/*@
predicate list(struct list_node* n) = 
  n == 0 ? emp : 
    n->value |-> _ &*& n->next |-> ?next &*& malloc_block_list_node(n) &*& list(next);
@*/

static int compare(struct list_node* n0, struct list_node* n1)
  //@ requires n0 != 0 &*& n1 != 0 &*& n0->value |-> _ &*& n0->next |-> _ &*& malloc_block_list_node(n0) &*& n1->value |-> _ &*& n1->next |-> _ &*& malloc_block_list_node(n1);
  //@ ensures n0->value |-> _ &*& n0->next |-> _ &*& malloc_block_list_node(n0) &*& n1->value |-> _ &*& n1->next |-> _ &*& malloc_block_list_node(n1);
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
  //@ requires pfirst != 0 &*& *pfirst |-> ?first &*& list(first);
  //@ ensures *pfirst |-> ?res &*& list(res);
{
  if (*pfirst == 0) {
    return;
  }  
  
  struct list_node* last_sorted = *pfirst;
  while (last_sorted->next != 0)
    //@ invariant pfirst != 0 &*& *pfirst |-> ?fst &*& list(fst) &*& last_sorted != 0 &*& malloc_block_list_node(last_sorted) &*& last_sorted->value |-> _ &*& last_sorted->next |-> _ &*& list(last_sorted->next);
  {
    struct list_node** pn = pfirst;
    
    //@ open list(*pn);
    //@ open list(last_sorted->next);
    int comparison = compare(*pn, last_sorted->next); 
    
    while (pn != &(last_sorted->next) && comparison < 0)
      //@ invariant pn != 0 &*& *pn |-> ?pnv &*& malloc_block_list_node(pnv) &*& pnv->value |-> _ &*& pnv->next |-> _ &*& list(pnv) &*& last_sorted != 0 &*& malloc_block_list_node(last_sorted) &*& last_sorted->value |-> _ &*& last_sorted->next |-> _ &*& list(last_sorted->next);
    { 
      pn = &((*pn)->next);
      if (pn != &(last_sorted->next)) {
        comparison = compare(*pn, last_sorted->next);
      }
    }
    
    if (pn != &(last_sorted->next)) {
      struct list_node* first_unsorted = last_sorted->next;
      last_sorted->next = first_unsorted->next;
      first_unsorted->next = *pn;
      *pn = first_unsorted;
    } else {
      last_sorted = last_sorted->next;
    }
  }
}

struct list_node* insertion_sort(struct list_node* l)
  //@ requires list(l);
  //@ ensures list(result);
{
  insertion_sort_core(&l);
  return l;
}