struct list_node {
  int value;
  struct list_node* next;
};

/*@
predicate lseg(struct list_node* from, struct list_node* to) =
  from == to ?
    true
  :
    from->value |-> ?v &*& from->next |-> ?n &*& lseg(n, to);

predicate nodes(struct list_node* n) =
  n == 0 ?
    true
  :
    n->value |-> ?v &*& n->next |-> ?nx &*& nodes(nx);
@*/

static int compare(struct list_node* n0, struct list_node* n1)
//@ requires n0->value |-> ?v0 &*& n1->value |-> ?v1;
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
//@ requires pfirst |-> ?f &*& nodes(f);
//@ ensures pfirst |-> ?f2 &*& nodes(f2);
{
  //@ open nodes(f);
  if (*pfirst == 0) {
    //@ close nodes(0);
    
    return;
  }  
  //@ assert f != 0;
  //@ assert (*pfirst)->value |-> ?fv &*& (*pfirst)->next |-> ?fn &*& nodes(fn);
  //@ close nodes(fn);
  //@ close nodes(*pfirst);
  
  struct list_node* last_sorted = *pfirst;
  //@ open nodes(*pfirst);
  while (last_sorted->next != 0)
    //@ invariant pfirst |-> ?h &*& nodes(h) &*& last_sorted != 0 &*& lseg(h, last_sorted) &*& last_sorted->value |-> ?lsv &*& last_sorted->next |-> ?lsn &*& nodes(lsn);
  {
    //@ open nodes(lsn);
    //@ assert lsn != 0;
    //@ close nodes(lsn);
    
    
    
    struct list_node** pn = pfirst;
    //@ struct list_node* first_unsorted0 = lsn;
    //@ close lseg(h, h);
    
    //@ open nodes(h);
    int comparison = compare(*pn, last_sorted->next); 
    //@ close nodes(h);
    
    while (pn != &(last_sorted->next) && comparison < 0)
      //@ invariant pfirst |-> h &*& lseg(h, *pn) &*& (*pn)->value |-> ?cv &*& (*pn)->next |-> ?cn &*& lseg(cn, last_sorted) &*& last_sorted->value |-> lsv &*& last_sorted->next |-> lsn &*& nodes(lsn);
    { 
      //@ open lseg(cn, last_sorted);
      //@ close lseg(*pn, *pn);
      //@ close lseg(h, *pn);
      //@ open lseg(h, *pn);
      //@ open lseg(*pn, *pn);
      //@ open lseg(cn, last_sorted);
      
      pn = &((*pn)->next);
      //@ close lseg(h, *pn);
      
      if (pn != &(last_sorted->next)) {
        //@ open lseg(h, *pn);
        //@ assert (*pn)->value |-> ?nv &*& (*pn)->next |-> ?nn &*& lseg(nn, last_sorted);
        //@ close lseg(h, *pn);
        comparison = compare(*pn, last_sorted->next);
      } else {
      }
    }
    
    //@ open lseg(h, *pn);
    //@ assert (*pn)->value |-> ?pnv &*& (*pn)->next |-> ?pnn &*& lseg(pnn, last_sorted);
    //@ close lseg(h, *pn);
    
    
    

    if (pn != &(last_sorted->next)) {
      struct list_node* first_unsorted = last_sorted->next;
      //@ open nodes(lsn);
      //@ assert first_unsorted->value |-> ?fuv &*& first_unsorted->next |-> ?fun &*& nodes(fun);
      
      
      last_sorted->next = first_unsorted->next;
      //@ close nodes(fun);
      
      first_unsorted->next = *pn;
      //@ open lseg(h, *pn);
      //@ open lseg(pnn, last_sorted);
      //@ close lseg(first_unsorted, *pn);
      //@ close lseg(h, first_unsorted);
      *pn = first_unsorted;
      
      //@ close lseg(h, last_sorted);
      //@ close nodes(lsn);
      //@ close nodes(h);
      
      

      
    } else {
      
      
      //@ open nodes(lsn);
      //@ assert lsn->value |-> ?nsv &*& lsn->next |-> ?nsn &*& nodes(nsn);
      //@ close lseg(h, last_sorted);
      //@ close lseg(last_sorted, lsn);
      //@ close lseg(h, lsn);
      last_sorted = last_sorted->next;
      //@ close nodes(nsn);
      //@ close nodes(last_sorted);
      //@ open nodes(last_sorted);
      //@ close nodes(h);
      
      
      
    }
    //@ open nodes(h);
    //@ open lseg(h, last_sorted);
    //@ close lseg(h, last_sorted);
  }
  //@ close nodes(lsn);
  //@ close lseg(h, last_sorted);
  //@ close nodes(h);
  
  
  
  
}

struct list_node* insertion_sort(struct list_node* l)
//@ requires nodes(l);
//@ ensures nodes(result);
{
  insertion_sort_core(&l);
  return l;
}