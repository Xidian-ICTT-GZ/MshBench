/*@ predicate list(struct list_node* node;) {
  switch (node) {
    case 0: return true;
    case _: return list(node->next);
  }
}
@*/

static int compare(struct list_node* n0, struct list_node* n1)
//@ requires list(n0) &*& list(n1);
//@ ensures list(n0) &*& list(n1);
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
//@ requires *pfirst |-> ?first &*& list(first);
//@ ensures *pfirst |-> ?sorted &*& list(sorted);
{
  if (*pfirst == 0) {
    //@ close list(0);
    return;
  }  
  
  struct list_node* last_sorted = *pfirst;
  //@ open list(last_sorted);
  while (last_sorted->next != 0)
  //@ invariant *pfirst |-> ?head &*& list(head) &*& last_sorted != 0 &*& list(last_sorted->next);
  {
    struct list_node** pn = pfirst;
    //@ open list(*pn);
    
    int comparison = compare(*pn, last_sorted->next); 
    
    while (pn != &(last_sorted->next) && comparison < 0)
    //@ invariant pn != &(last_sorted->next) ? (*pn |-> ?curr &*& list(curr) &*& curr != 0) : true;
    //@ invariant pn != &(last_sorted->next) ? (list(last_sorted->next)) : true;
    { 
      pn = &((*pn)->next);
      
      if (pn != &(last_sorted->next)) {
        //@ open list(*pn);
        comparison = compare(*pn, last_sorted->next);
      } else {
      }
    }
    
    if (pn != &(last_sorted->next)) {
      struct list_node* first_unsorted = last_sorted->next;
      
      last_sorted->next = first_unsorted->next;
      
      first_unsorted->next = *pn;
      *pn = first_unsorted;
      
      //@ close list(first_unsorted);
    } else {
      last_sorted = last_sorted->next;
      //@ open list(last_sorted);
    }
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