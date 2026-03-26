struct list_node {
  int value;
  struct list_node* next;
};

/*@
predicate list_node(struct list_node* n; int value, struct list_node* next) =
  n->value |-> value &*& n->next |-> next &*& malloc_block_list_node(n);
@*/

/*@
predicate list(struct list_node* n;) =
  n == 0 ? true : list_node(n, ?v, ?next) &*& list(next);
@*/

static int compare(struct list_node* n0, struct list_node* n1)
//@ requires list_node(n0, ?v0, ?next0) &*& list_node(n1, ?v1, ?next1);
//@ ensures list_node(n0, v0, next0) &*& list_node(n1, v1, next1);
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
    return;
  }
  //@ open list(first);
  struct list_node* last_sorted = *pfirst;
  //@ assert list_node(last_sorted, ?val, ?next_part);
  //@ close list(next_part);
  while (last_sorted->next != 0)
  //@ invariant list_node(last_sorted, ?last_val, ?next_part) &*& list(next_part) &*& *pfirst |-> ?sorted_prefix &*& list(sorted_prefix);
  {
    //@ open list(next_part);
    struct list_node** pn = pfirst;
    //@ open list(sorted_prefix);
    int comparison = compare(*pn, last_sorted->next);
    //@ close list(sorted_prefix);
    while (pn != &(last_sorted->next) && comparison < 0)
    //@ invariant *pn |-> ?cur_inner &*& list(cur_inner) &*& list_node(last_sorted, last_val, next_part) &*& list_node(last_sorted->next, ?unsorted_val, ?unsorted_next) &*& list(unsorted_next);
    {
      pn = &((*pn)->next);
      if (pn != &(last_sorted->next)) {
        //@ open list(*pn);
        comparison = compare(*pn, last_sorted->next);
        //@ close list(*pn);
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
}

struct list_node* insertion_sort(struct list_node* l)
//@ requires list(l);
//@ ensures list(result);
{
  insertion_sort_core(&l);
  return l;
}