struct list_node
{
  int value;
  struct list_node *next;
};

/*@
predicate lseg(struct list_node *from, struct list_node *to; list<int> vs) =
  from == to ?
    vs == nil
  :
    from != 0 &*& from->value |-> ?v &*& from->next |-> ?next &*& 
    lseg(next, to, ?vs_tail) &*& vs == cons(v, vs_tail);

predicate list(struct list_node *l; list<int> vs) =
  lseg(l, 0, vs);
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
//@ requires pointer(pfirst, ?l) &*& list(l, ?vs);
//@ ensures pointer(pfirst, ?l2) &*& list(l2, ?vs2);
{
  if (*pfirst == 0)
  {
    //@ open list(0, _);
    //@ close list(0, nil);
    return;
  }
  //@ open list(l, vs);
  //@ open lseg(l, 0, vs);
  struct list_node *last_sorted = *pfirst;
  //@ close lseg(last_sorted, last_sorted, nil);
  while (last_sorted->next != 0)
  //@ invariant pointer(pfirst, ?first) &*& lseg(first, last_sorted, ?vs1) &*& last_sorted != 0 &*& last_sorted->value |-> ?lsv &*& last_sorted->next |-> ?nxt &*& lseg(nxt, 0, ?vs2);
  {
    //@ open lseg(nxt, 0, vs2);
    struct list_node **pn = pfirst;
    //@ close lseg(*pfirst, *pfirst, nil);
    int comparison = compare(*pn, last_sorted->next);

    while (pn != &(last_sorted->next) && comparison < 0)
    //@ invariant pointer(pn, ?pnv) &*& pnv != 0 &*& lseg(pnv, last_sorted, ?vsmid) &*& last_sorted->value |-> lsv &*& last_sorted->next |-> nxt &*& nxt != 0 &*& nxt->value |-> ?nxtv &*& nxt->next |-> ?nxtnxt &*& lseg(nxtnxt, 0, ?vstail) &*& pointer(pfirst, first) &*& lseg(first, pnv, ?vspre);
    {
      //@ open lseg(pnv, last_sorted, vsmid);
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
      //@ close lseg(first_unsorted, last_sorted, _);
    }
    else
    {
      //@ open lseg(nxt, last_sorted, _);
      last_sorted = last_sorted->next;
      //@ close lseg(last_sorted, last_sorted, nil);
    }
  }
  //@ open lseg(0, 0, _);
  //@ close lseg(0, 0, nil);
  //@ close list(_, _);
}

struct list_node *insertion_sort(struct list_node *l)
//@ requires list(l, ?vs);
//@ ensures list(result, ?vs2);
{
  //@ close pointer(&l, l);
  insertion_sort_core(&l);
  //@ open pointer(&l, ?l2);
  return l;
}