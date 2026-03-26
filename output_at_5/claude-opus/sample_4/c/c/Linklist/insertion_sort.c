struct list_node {
  int value;
  struct list_node* next;
};

/*@
predicate list_node(struct list_node* n) = 
  n->value |-> _ &*& n->next |-> _ &*& malloc_block_list_node(n);

predicate list(struct list_node* n) =
  n == 0 ? emp : list_node(n) &*& list(n->next);
@*/

static int compare(struct list_node* n0, struct list_node* n1)
  //@ requires list_node(n0) &*& list_node(n1);
  //@ ensures list_node(n0) &*& list_node(n1);
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
  //@ open list(last_sorted);
  while (last_sorted->next != 0)
    //@ invariant pfirst != 0 &*& *pfirst |-> ?fst &*& list(fst) &*& last_sorted != 0 &*& list(last_sorted);
  {
    struct list_node** pn = pfirst;
    //@ open list(*pn);
    int comparison = compare(*pn, last_sorted->next); 
    
    while (pn != &(last_sorted->next) && comparison < 0)
      //@ invariant pn != 0 &*& *pn |-> ?pnv &*& malloc_block_list_node(pnv) &*& pnv->value |-> _ &*& pnv->next |-> _ &*& list(pnv) &*& last_sorted != 0 &*& list(last_sorted);
    { 
      pn = &((*pn)->next);
      if (pn != &(last_sorted->next)) {
        //@ open list(*pn);
        comparison = compare(*pn, last_sorted->next);
      }
    }
    
    if (pn != &(last_sorted->next)) {
      struct list_node* first_unsorted = last_sorted->next;
      //@ open list(first_unsorted);
      last_sorted->next = first_unsorted->next;
      first_unsorted->next = *pn;
      *pn = first_unsorted;
      //@ close list(first_unsorted);
    } else {
      last_sorted = last_sorted->next;
    }
    //@ close list(last_sorted);
  }
  //@ close list(*pfirst);
}

struct list_node* insertion_sort(struct list_node* l)
  //@ requires list(l);
  //@ ensures list(result);
{
  insertion_sort_core(&l);
  return l;
}