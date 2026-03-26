/*@
predicate list_node(struct list_node* node; int value, struct list_node* next) =
    node != 0 &*&
    node->value |-> value &*&
    node->next |-> next &*&
    malloc_block_list_node(node);
@*/

/*@
predicate list(struct list_node* head;) =
    head == 0 ?
        true
    :
        list_node(head, ?v, ?n) &*& list(n);
@*/

struct list_node {
  int value;
  struct list_node* next;
};

static int compare(struct list_node* n0, struct list_node* n1)
//@ requires list_node(n0, ?v0, ?nxt0) &*& list_node(n1, ?v1, ?nxt1);
//@ ensures list_node(n0, v0, nxt0) &*& list_node(n1, v1, nxt1);
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
    //@ close list(0);
    return;
  }  
  //@ open list(first);
  //@ assert list_node(first, ?fv, ?fn) &*& list(fn);
  struct list_node* last_sorted = *pfirst;
  //@ close list(fn);
  //@ close list(last_sorted);
  while (last_sorted->next != 0)
  //@ invariant list(last_sorted) &*& *pfirst |-> ?cur_first &*& list(cur_first);
  {
    //@ open list(last_sorted);
    //@ assert list_node(last_sorted, ?lv, ?ln) &*& list(ln);
    //@ open list(ln);
    //@ assert list_node(ln, ?unsorted_val, ?unsorted_next) &*& list(unsorted_next);
    struct list_node** pn = pfirst;
    //@ assert *pn |-> cur_first;
    //@ close list(unsorted_next);
    //@ close list(ln);
    //@ close list(last_sorted);
    int comparison = compare(*pn, last_sorted->next); 
    //@ open list(cur_first);
    //@ assert list_node(cur_first, ?cv, ?cn) &*& list(cn);
    //@ close list(cn);
    //@ close list(cur_first);
    
    while (pn != &(last_sorted->next) && comparison < 0)
    //@ invariant *pn |-> ?pn_val &*& list(pn_val) &*& pn == &(last_sorted->next) ? true : list(last_sorted);
    { 
      pn = &((*pn)->next);
      //@ open list(pn_val);
      //@ assert list_node(pn_val, ?pv, ?pnext) &*& list(pnext);
      //@ close list(pnext);
      //@ close list(pn_val);
      
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