struct list_node
{
  int value;
  struct list_node *next;
};

/*@

predicate nodes(struct list_node *n) =
  n == 0 ?
    true
  :
    n->value |-> ?v &*& n->next |-> ?nx &*& malloc_block_list_node(n) &*& nodes(nx);

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
//@ requires pfirst |-> ?f &*& nodes(f);
//@ ensures pfirst |-> ?f2 &*& nodes(f2);
{
  if (*pfirst == 0)
  {

    return;
  }

  struct list_node *last_sorted = *pfirst;
  while (last_sorted->next != 0)

  {

    struct list_node **pn = pfirst;

    int comparison = compare(*pn, last_sorted->next);

    while (pn != &(last_sorted->next) && comparison < 0)

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
  }
}

struct list_node *insertion_sort(struct list_node *l)
//@ requires nodes(l);
//@ ensures nodes(result);
{
  insertion_sort_core(&l);
  return l;
}