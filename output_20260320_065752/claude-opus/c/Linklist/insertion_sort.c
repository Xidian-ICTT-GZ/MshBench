struct list_node {
  int value;
  struct list_node* next;
};

/*@ predicate list(struct list_node* n) =
      n == 0 ? true : 
      n->next |-> ?next &*& n->value |-> _ &*& malloc_block_list_node(n) &*& list(next);
@*/

//@ requires list(n);
//@ ensures list(n);
static int compare(struct list_node* n0, struct list_node* n1)
{
  //@ open list(n0);
  //@ open list(n1);
  if (n0->value < n1->value) {
    //@ close list(n0);
    //@ close list(n1);
    return -1;
  } else if (n0->value > n1->value) {
    //@ close list(n0);
    //@ close list(n1);
    return 1;
  } else {
    //@ close list(n0);
    //@ close list(n1);
    return 0;
  }
}

//@ requires *pfirst |-> ?first &*& list(first);
//@ ensures *pfirst |-> first &*& list(first);
void insertion_sort_core(struct list_node** pfirst)
{
  //@ open *pfirst |-> ?first &*& list(first);
  if (*pfirst == 0) {    
    //@ close list(0);
    return;
  }
  //@ open list(*pfirst);
  struct list_node* last_sorted = *pfirst;
  //@ open list(last_sorted);
  while (last_sorted->next != 0)
    //@ invariant *pfirst |-> ?first &*& list(first) &*& list(last_sorted) &*& ?lsnext = last_sorted->next &*& list(lsnext);
  {
    //@ open list(last_sorted);
    //@ open list(last_sorted->next);

    struct list_node** pn = pfirst;
    //@ open list(*pn);
    int comparison = compare(*pn, last_sorted->next); 

    while (pn != &(last_sorted->next) && comparison < 0)
      //@ invariant pfirst <= pn && pn <= &(last_sorted->next) &*& 
      //@  (*pfirst |-> ?f &*& list(f)) &*& list(last_sorted) &*& list(last_sorted->next);
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

 //@ requires list(l);
//@ ensures list(result);
struct list_node* insertion_sort(struct list_node* l)
{
  insertion_sort_core(&l);
  return l;
}