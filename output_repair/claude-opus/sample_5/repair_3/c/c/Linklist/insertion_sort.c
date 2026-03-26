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

/*@
predicate lseg(struct list_node *from, struct list_node *to;) =
  from == to ?
    emp
  :
    from->value |-> _ &*& from->next |-> ?next &*& lseg(next, to);
@*/

/*@
lemma void lseg_append(struct list_node *from, struct list_node *to)
  requires lseg(from, to) &*& to->value |-> _ &*& to->next |-> ?next &*& list(next);
  ensures list(from);
{
  open lseg(from, to);
  if (from == to) {
    close list(next);
    close list(to);
  } else {
    lseg_append(from->next, to);
    close list(from);
  }
}
@*/

static int compare(struct list_node *n0, struct list_node *n1)
//@ requires n0->value |-> ?v0 &*& n1->value |-> ?v1;
//@ ensures n0->value |-> v0 &*& n1->value |-> v1 &*& (result == -1 || result == 0 || result == 1);
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
//@ requires pfirst != 0 &*& *pfirst |-> ?first &*& list(first);
//@ ensures *pfirst |-> ?sorted &*& list(sorted);
{
  if (*pfirst == 0)
  {
    //@ open list(0);
    return;
  }

  struct list_node *last_sorted = *pfirst;
  //@ open list(last_sorted);
  while (last_sorted->next != 0)
  //@ invariant *pfirst |-> ?pf &*& lseg(pf, last_sorted) &*& last_sorted->value |-> _ &*& last_sorted->next |-> ?ls_next &*& list(ls_next);
  {
    //@ open list(ls_next);
    struct list_node **pn = pfirst;

    //@ close list(ls_next);
    //@ close lseg(last_sorted, last_sorted);

    int comparison = compare(*pn, last_sorted->next);

    while (pn != &(last_sorted->next) && comparison < 0)
    //@ invariant lseg(pf, ?cur) &*& cur->value |-> _ &*& cur->next |-> ?cur_next &*& lseg(cur_next, last_sorted) &*& last_sorted->value |-> _ &*& last_sorted->next |-> ls_next &*& list(ls_next) &*& *pn |-> cur &*& pn == &cur->next || pn == pfirst;
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
  //@ lseg_append(pf, last_sorted);
  //@ close list(last_sorted);
}

struct list_node *insertion_sort(struct list_node *l)
//@ requires list(l);
//@ ensures list(result);
{
  insertion_sort_core(&l);
  return l;
}