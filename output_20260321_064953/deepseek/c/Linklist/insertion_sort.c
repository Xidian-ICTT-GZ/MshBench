struct list_node {
  int value;
  struct list_node* next;
};

/*@
predicate nodes(struct list_node* n;) =
  n == 0 ?
    true
  :
    n->value |-> _ &*& n->next |-> ?next &*& nodes(next);
@*/

/*@
lemma void nodes_split(struct list_node* n)
  requires nodes(n) &*& n != 0;
  ensures n->value |-> _ &*& n->next |-> ?next &*& nodes(next);
{
  open nodes(n);
}
@*/

/*@
lemma void nodes_merge(struct list_node* n)
  requires n->value |-> _ &*& n->next |-> ?next &*& nodes(next);
  ensures nodes(n);
{
  close nodes(n);
}
@*/

static int compare(struct list_node* n0, struct list_node* n1)
//@ requires nodes(n0) &*& nodes(n1);
//@ ensures nodes(n0) &*& nodes(n1);
{
  //@ open nodes(n0);
  //@ open nodes(n1);
  if (n0->value < n1->value) {
    //@ close nodes(n1);
    //@ close nodes(n0);
    return -1;
  } else if (n0->value > n1->value) {
    //@ close nodes(n1);
    //@ close nodes(n0);
    return 1;
  } else {
    //@ close nodes(n1);
    //@ close nodes(n0);
    return 0;
  }
}

void insertion_sort_core(struct list_node** pfirst)
//@ requires *pfirst |-> ?first &*& nodes(first);
//@ ensures *pfirst |-> ?first1 &*& nodes(first1);
{
  //@ open nodes(first);
  if (*pfirst == 0) {
    //@ close nodes(0);
    return;
  }
  //@ close nodes(first);
  struct list_node* last_sorted = *pfirst;
  //@ struct list_node* first_ghost = *pfirst;
  //@ assert nodes(first_ghost);
  //@ open nodes(first_ghost);
  //@ struct list_node* next_ghost = last_sorted->next;
  //@ close nodes(next_ghost);
  //@ close nodes(last_sorted);
  while (last_sorted->next != 0)
  //@ invariant *pfirst |-> ?cur_first &*& nodes(cur_first);
  {
    struct list_node** pn = pfirst;
    //@ assert *pn |-> ?pn_val;
    //@ open nodes(pn_val);
    //@ close nodes(pn_val);
    int comparison = compare(*pn, last_sorted->next);
    //@ assert nodes(*pn);
    //@ assert nodes(last_sorted->next);
    while (pn != &(last_sorted->next) && comparison < 0)
    //@ invariant *pfirst |-> ?cur_first_inner &*& nodes(cur_first_inner);
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
}

struct list_node* insertion_sort(struct list_node* l)
//@ requires nodes(l);
//@ ensures nodes(result);
{
  insertion_sort_core(&l);
  return l;
}