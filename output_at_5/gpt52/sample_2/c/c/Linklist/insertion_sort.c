struct list_node {
  int value;
  struct list_node* next;
};

/*@
predicate nodes(struct list_node* n) =
  n == 0 ?
    true
  :
    n->value |-> ?v &*& n->next |-> ?nx &*& nodes(nx);
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
//@ requires *pfirst |-> ?f &*& nodes(f);
//@ ensures *pfirst |-> ?f2 &*& nodes(f2);
{
  //@ open nodes(f);
  if (*pfirst == 0) {
    //@ close nodes(0);
    
    return;
  }  
  //@ assert *pfirst != 0;
  //@ assert (*pfirst)->value |-> ?v &*& (*pfirst)->next |-> ?n &*& nodes(n);
  //@ close nodes(*pfirst);

  struct list_node* last_sorted = *pfirst;
  //@ open nodes(*pfirst);
  //@ assert last_sorted->value |-> ?lsv &*& last_sorted->next |-> ?lsn &*& nodes(lsn);
  while (last_sorted->next != 0)
    //@ invariant last_sorted != 0 &*& last_sorted->value |-> lsv &*& last_sorted->next |-> lsn &*& nodes(lsn);
  {
    struct list_node** pn = pfirst;
    
    //@ open nodes(lsn);
    //@ assert lsn != 0;
    //@ assert lsn->value |-> ?fuv &*& lsn->next |-> ?fun &*& nodes(fun);
    //@ close nodes(lsn);

    //@ open nodes(f);
    //@ assert (*pfirst)->value |-> ?hv &*& (*pfirst)->next |-> ?hn &*& nodes(hn);
    //@ close nodes(f);
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
      
      
      //@ open nodes(lsn);
      //@ assert lsn->value |-> ?nsv &*& lsn->next |-> ?nsn &*& nodes(nsn);
      last_sorted = last_sorted->next;
      //@ close nodes(last_sorted);
      //@ open nodes(last_sorted);
      //@ assert last_sorted->value |-> lsv &*& last_sorted->next |-> lsn &*& nodes(lsn);
      
    }
  }
  //@ close nodes(lsn);
  //@ close nodes(last_sorted);
  //@ close nodes(f);
}

struct list_node* insertion_sort(struct list_node* l)
//@ requires nodes(l);
//@ ensures nodes(result);
{
  insertion_sort_core(&l);
  return l;
}