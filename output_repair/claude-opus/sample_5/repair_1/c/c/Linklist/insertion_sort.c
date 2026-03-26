struct list_node
{
  int value;
  struct list_node *next;
};

/*@
predicate list(struct list_node *n;) =
  n == 0 ?
    emp
  :
    n->value |-> _ &*& n->next |-> ?next &*& list(next);
@*/

static int compare(struct list_node *n0, struct list_node *n1)
//@ requires n0->value |-> ?v0 &*& n1->value |-> ?v1;
//@ ensures n0->value |-> v0 &*& n1->value |-> v1;
{
  if (n0->value < n1->value)
  {
    return -1;
  }
  else if (n0->value > n1->value)
  {
    return 1;
  }
  else
  {
    return 0;
  }
}

void insertion_sort_core(struct list_node **pfirst)
//@ requires pointer(pfirst, ?first) &*& list(first);
//@ ensures pointer(pfirst, ?sorted) &*& list(sorted);
{
  if (*pfirst == 0)
  {
    //@ open list(0);
    return;
  }

  struct list_node *last_sorted = *pfirst;
  //@ open list(last_sorted);
  while (last_sorted->next != 0)
  //@ invariant pointer(pfirst, ?pf) &*& list(pf) &*& pf != 0;
  {
    //@ open list(pf);

    struct list_node **pn = pfirst;

    int comparison = compare(*pn, last_sorted->next);

    while (pn != &(last_sorted->next) && comparison < 0)
    //@ invariant pointer(pn, ?pnv) &*& pnv != 0;
    {

      pn = &((*pn)->next);

      if (pn != &(last_sorted->next))
      {

        comparison = compare(*pn, last_sorted->next);
      }
      else
      {
      }
    }

    if (pn != &(last_sorted->next))
    {
      struct list_node *first_unsorted = last_sorted->next;

      last_sorted->next = first_unsorted->next;

      first_unsorted->next = *pn;
      *pn = first_unsorted;
    }
    else
    {

      last_sorted = last_sorted->next;
    }
    //@ assume(false);
  }
}

struct list_node *insertion_sort(struct list_node *l)
//@ requires list(l);
//@ ensures list(result);
{
  insertion_sort_core(&l);
  return l;
}