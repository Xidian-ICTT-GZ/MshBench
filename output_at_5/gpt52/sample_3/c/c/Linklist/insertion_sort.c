struct list_node {
  int value;
  struct list_node* next;
};

/*@
predicate nodes(struct list_node* n) =
  n == 0 ?
    true
  :
    n->value |-> _ &*& n->next |-> ?nx &*& nodes(nx);

predicate list_ptr(struct list_node** p; struct list_node* v) =
  p |-> v;
@*/

static int compare(struct list_node* n0, struct list_node* n1)
//@ requires n0 != 0 &*& n1 != 0 &*& n0->value |-> ?v0 &*& n1->value |-> ?v1;
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
//@ requires list_ptr(pfirst, ?f) &*& nodes(f);
//@ ensures list_ptr(pfirst, ?f2) &*& nodes(f2);
{
  //@ open list_ptr(pfirst, f);
  //@ open nodes(f);
  if (*pfirst == 0) {
    //@ close nodes(0);
    //@ close list_ptr(pfirst, 0);
    return;
  }  
  //@ close nodes(f);
  //@ close list_ptr(pfirst, f);

  //@ open list_ptr(pfirst, f);
  struct list_node* last_sorted = *pfirst;
  //@ close list_ptr(pfirst, f);
  //@ open nodes(last_sorted);
  while (last_sorted->next != 0)
  //@ invariant nodes(last_sorted) &*& last_sorted != 0;
  {
    //@ open nodes(last_sorted);
    struct list_node** pn = pfirst;
    //@ close nodes(last_sorted);
    
    //@ open list_ptr(pfirst, f);
    //@ close list_ptr(pfirst, f);
    //@ open nodes(last_sorted);
    //@ assert last_sorted->next |-> ?lsn;
    //@ close nodes(last_sorted);
    //@ open nodes(f);
    //@ close nodes(f);
    //@ open nodes(lsn);
    //@ close nodes(lsn);
    int comparison = compare(*pn, last_sorted->next); 
    
    while (pn != &(last_sorted->next) && comparison < 0)
    //@ invariant true;
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
      //@ open nodes(last_sorted);
      last_sorted = last_sorted->next;
      //@ close nodes(last_sorted);
    }
  }
  //@ close nodes(last_sorted);
}

struct list_node* insertion_sort(struct list_node* l)
//@ requires nodes(l);
//@ ensures nodes(result);
{
  insertion_sort_core(&l);
  return l;
}