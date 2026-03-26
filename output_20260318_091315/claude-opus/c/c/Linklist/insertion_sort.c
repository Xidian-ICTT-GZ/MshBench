struct list_node {
  int value;
  struct list_node* next;
};

/*@ predicate list(struct list_node* n;) =
      n == 0 ? 
        true 
      : 
        n->value |-> _ &*& n->next |-> ?next &*& list(next);
@*/

/*@ predicate sorted(struct list_node* n;) =
      n == 0 ? 
        true 
      : 
        n->next == 0 ? list(n)
      : 
        n->value <= n->next->value &*& 
        n->value |-> _ &*& n->next |-> ?next &*&
        sorted(next);
@*/

static int compare(struct list_node* n0, struct list_node* n1)
  //@ requires n0 != 0 &*& n1 != 0 &*& n0->value |-> ?v0 &*& n1->value |-> ?v1;
  //@ ensures n0->value |-> v0 &*& n1->value |-> v1 &*& (result == -1 || result == 0 || result == 1);
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
  //@ ensures pfirst != 0 &*& *pfirst |-> ?res &*& sorted(res);
{
  if (*pfirst == 0) {
    return;
  }  

  struct list_node* last_sorted = *pfirst;

  //@ open list(last_sorted);
  while (last_sorted->next != 0)
    //@ invariant list(*pfirst) &*& sorted_upto(*pfirst, last_sorted) &*& last_sorted != 0 &*& last_sorted->next |-> _;
  {
    struct list_node** pn = pfirst;
    
    int comparison = compare(*pn, last_sorted->next); 
    //@ open list(*pn);
    while (pn != &(last_sorted->next) && comparison < 0)
      //@ invariant pn != 0 &*& *pn |-> ?cur &*& list(cur) &*& pn != &(last_sorted->next);
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

/*@ predicate sorted_upto(struct list_node* start, struct list_node* upto) =
      start == upto ? true :
      start != 0 &*& start->next != 0 &*&
      start->value <= start->next->value &*&
      sorted_upto(start->next, upto);
@*/

struct list_node* insertion_sort(struct list_node* l)
  //@ requires list(l);
  //@ ensures sorted(result);
{
  insertion_sort_core(&l);
  return l;
}