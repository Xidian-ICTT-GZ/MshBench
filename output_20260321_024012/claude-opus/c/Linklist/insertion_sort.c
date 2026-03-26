struct list_node {
  int value;
  struct list_node* next;
};
/*@
predicate list(struct list_node* n) =
  n == 0 ?
    emp
  :
    malloc_block_list_node(n) &*&
    list(n->next);
@*/

static int compare(struct list_node* n0, struct list_node* n1)
  //@ requires n0 != 0 &*& n1 != 0 &*& malloc_block_list_node(n0) &*& malloc_block_list_node(n1);
  //@ ensures  (result == -1 && n0->value < n1->value) || (result == 1 && n0->value > n1->value) || (result == 0 && n0->value == n1->value);
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
  //@ requires pfirst != 0 &*& ( (*pfirst == 0) || malloc_block_list_node(*pfirst) ) &*& ( (*pfirst == 0) || list(*pfirst) );
  //@ ensures true;
{
  if (*pfirst == 0) {
    
    return;
  }  
  
  struct list_node* last_sorted = *pfirst;
  //@ open list(last_sorted);
  while (last_sorted->next != 0)
    //@ invariant malloc_block_list_node(last_sorted) &*& list(last_sorted->next) &*& (last_sorted != 0);
  {
    struct list_node** pn = pfirst;
    //@ open list(*pn);
    
    int comparison = compare(*pn, last_sorted->next); 
    
    while (pn != &(last_sorted->next) && comparison < 0)
      //@ invariant pn != 0 &*& malloc_block_list_node(*pn) &*& *pn != 0;
    { 
      pn = &((*pn)->next);
      
      if (pn != &(last_sorted->next)) {
        comparison = compare(*pn, last_sorted->next);
      } else {
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
  //@ close list(*pfirst);
}

struct list_node* insertion_sort(struct list_node* l)
  //@ requires l == 0 || list(l);
  //@ ensures l == 0 || list(result);
{
  insertion_sort_core(&l);
  return l;
}