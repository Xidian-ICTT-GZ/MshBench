/*@
predicate list(struct list_node* n;) =
  n == 0 ?
    emp
  :
    n->value |-> ?v &*& n->next |-> ?next &*& list(next);
@*/

static int compare(struct list_node* n0, struct list_node* n1)
//@ requires n0->value |-> ?v0 &*& n1->value |-> ?v1;
//@ ensures n0->value |-> v0 &*& n1->value |-> v1 &*& result == (v0 < v1 ? -1 : v0 > v1 ? 1 : 0);
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
  struct list_node* last_sorted = *pfirst;
  //@ open list(last_sorted);
  //@ close list(last_sorted);
  while (last_sorted->next != 0)
  //@ invariant *pfirst |-> ?sorted_prefix &*& list(sorted_prefix) &*& last_sorted->next |-> ?rest &*& list(rest);
  {
    struct list_node** pn = pfirst;
    int comparison = compare(*pn, last_sorted->next);
    while (pn != &(last_sorted->next) && comparison < 0)
    //@ invariant *pfirst |-> ?sorted_prefix2 &*& list(sorted_prefix2) &*& last_sorted->next |-> ?rest2 &*& list(rest2);
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
//@ requires list(l);
//@ ensures list(result);
{
  insertion_sort_core(&l);
  return l;
}