struct list_node {
  int value;
  struct list_node* next;
};

/*@ predicate nodes(struct list_node* first;) =
  first == 0 ?
    emp
  :
    first->value |-> _ &*& first->next |-> ?next &*& malloc_block_list_node(first) &*& nodes(next);
@*/

static int compare(struct list_node* n0, struct list_node* n1)
/*@ requires nodes(n0) &*& nodes(n1); @*/
/*@ ensures nodes(n0) &*& nodes(n1); @*/
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
/*@ requires pfirst != 0 &*&
             malloc_block_ptr(pfirst) &*&
             (*pfirst == 0 ? emp : nodes(*pfirst)); @*/
/*@ ensures pfirst != 0 &*&
            malloc_block_ptr(pfirst) &*&
            (*pfirst == 0 ? emp : nodes(*pfirst)); @*/
{
  if (*pfirst == 0) {
    return;
  }  
  
  struct list_node* last_sorted = *pfirst;
  //@ open nodes(*pfirst);
  while (last_sorted->next != 0)
  //@ invariant nodes(*pfirst) &*& last_sorted != 0 &*& last_sorted->next != 0;
  {
    struct list_node** pn = pfirst;
    int comparison = compare(*pn, last_sorted->next);
    
    while (pn != &(last_sorted->next) && comparison < 0)
    //@ invariant nodes(*pfirst);
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
/*@ requires l == 0 ? emp : nodes(l); @*/
/*@ ensures l == 0 ? emp : nodes(result); @*/
{
  insertion_sort_core(&l);
  return l;
}