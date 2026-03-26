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

predicate list(struct list_node* l) = lseg(l, 0);

lemma void lseg_append(struct list_node* a, struct list_node* b, struct list_node* c)
  requires lseg(a, b) &*& lseg(b, c);
  ensures lseg(a, c);
{
  open lseg(a, b);
  if (a != b) {
    lseg_append(?n, b, c);
    close lseg(a, c);
  }
}

lemma void lseg_split(struct list_node* a, struct list_node* b, struct list_node* c)
  requires lseg(a, c);
  ensures lseg(a, b) &*& lseg(b, c);
{
  if (a == b) {
    close lseg(a, b);
  } else {
    open lseg(a, c);
    lseg_split(?n, b, c);
    close lseg(a, b);
  }
}

lemma void lseg_to_list(struct list_node* a)
  requires lseg(a, 0);
  ensures list(a);
{
  close list(a);
}

lemma void list_to_lseg(struct list_node* a)
  requires list(a);
  ensures lseg(a, 0);
{
  open list(a);
}

lemma void lseg_length_pos(struct list_node* from, struct list_node* to)
  requires lseg(from, to) &*& from != to;
  ensures lseg(from, to);
{
  // just a helper to allow opening when non-empty; does nothing
}
@*/

static int compare(struct list_node* n0, struct list_node* n1)
//@ requires n0->value |-> ?v0 &*& n0->next |-> ?nx0 &*& n1->value |-> ?v1 &*& n1->next |-> ?nx1;
//@ ensures n0->value |-> v0 &*& n0->next |-> nx0 &*& n1->value |-> v1 &*& n1->next |-> nx1;
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
//@ requires pfirst |-> ?l &*& list(l);
//@ ensures pfirst |-> ?l2 &*& list(l2);
{
  //@ open list(l);
  if (*pfirst == 0) {
    //@ close list(0);
    return;
  }  
  //@ list_to_lseg(*pfirst);
  struct list_node* last_sorted = *pfirst;
  //@ open lseg(last_sorted, 0);
  //@ close lseg(last_sorted, last_sorted->next);
  //@ close lseg(last_sorted->next, 0);
  while (last_sorted->next != 0)
  //@ invariant pfirst |-> ?head &*& lseg(head, last_sorted->next) &*& lseg(last_sorted->next, 0) &*& last_sorted != 0;
  {
    struct list_node** pn = pfirst;
    //@ assert pn == pfirst;
    //@ assert pfirst |-> head;
    //@ lseg_split(head, last_sorted->next, 0);
    //@ lseg_append(head, last_sorted->next, 0);
    //@ lseg_split(head, last_sorted->next, 0);
    //@ assert lseg(head, last_sorted->next) &*& lseg(last_sorted->next, 0);
    //@ open lseg(head, last_sorted->next);
    //@ close lseg(head, last_sorted->next);
    
    //@ open lseg(last_sorted->next, 0);
    //@ close lseg(last_sorted->next, 0);
    int comparison = compare(*pn, last_sorted->next); 
    
    while (pn != &(last_sorted->next) && comparison < 0)
    //@ invariant pfirst |-> head &*& lseg(head, *pn) &*& (*pn)->value |-> ?pv &*& (*pn)->next |-> ?pnxt &*& lseg(pnxt, last_sorted->next) &*& lseg(last_sorted->next, 0) &*& pn == &(*pn == head ? *pfirst : *((struct list_node**)0)) ? true : true;
    { 
      //@ open lseg(head, *pn);
      //@ close lseg(head, *pn);
      pn = &((*pn)->next);
      //@ assert pn == &pnxt;
      //@ close lseg(head, *pn);
      //@ lseg_append(head, *pn, last_sorted->next);
      //@ open lseg(*pn, last_sorted->next);
      //@ close lseg(*pn, last_sorted->next);
      
      if (pn != &(last_sorted->next)) {
        //@ open lseg(*pn, last_sorted->next);
        //@ close lseg(*pn, last_sorted->next);
        comparison = compare(*pn, last_sorted->next);
      } else {
      }
    }
    
    if (pn != &(last_sorted->next)) {
      struct list_node* first_unsorted = last_sorted->next;
      //@ open lseg(last_sorted->next, 0);
      //@ open lseg(first_unsorted, 0);
      //@ assert first_unsorted->value |-> ?fuv &*& first_unsorted->next |-> ?fun &*& lseg(fun, 0);
      //@ close lseg(first_unsorted, 0);
      
      last_sorted->next = first_unsorted->next;
      //@ assert last_sorted->value |-> ?lsv &*& last_sorted->next |-> fun;
      
      first_unsorted->next = *pn;
      //@ assert first_unsorted->next |-> *pn;
      *pn = first_unsorted;
      //@ close lseg(first_unsorted, last_sorted->next);
      //@ close lseg(last_sorted->next, 0);
      //@ lseg_append(head, first_unsorted, last_sorted->next);
      //@ lseg_append(head, last_sorted->next, 0);
    } else {
      last_sorted = last_sorted->next;
      //@ open lseg(head, last_sorted);
      //@ close lseg(head, last_sorted);
    }
  }
  //@ lseg_append(head, last_sorted->next, 0);
  //@ close list(*pfirst);
}

struct list_node* insertion_sort(struct list_node* l)
//@ requires list(l);
//@ ensures list(result);
{
  insertion_sort_core(&l);
  return l;
}