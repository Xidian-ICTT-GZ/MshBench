/*@ predicate list(struct list_node* node; int length) =
  (node == 0 ? length == 0 :
   node->next |-> ?next &*&
   node->value |-> _ &*&
   malloc_block_list_node(node) &*&
   list(next, length - 1));
@*/

static int compare(struct list_node* n0, struct list_node* n1)
//@ requires list(n0, _) &*& list(n1, _);
//@ ensures list(n0, _) &*& list(n1, _);
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
//@ requires *pfirst |-> ?first &*& list(first, ?n);
//@ ensures *pfirst |-> ?sorted &*& list(sorted, n);
{
  if (*pfirst == 0) {
    //@ close list(0, 0);
    return;
  }  
  
  struct list_node* last_sorted = *pfirst;
  //@ open list(last_sorted, n);
  //@ assert last_sorted->next |-> ?next0;
  //@ assert malloc_block_list_node(last_sorted);
  //@ close list(last_sorted, 1); // temporary closure for the sorted part
  //@ list_split: lemma void split_list(struct list_node* hd, int len) 
  //@   requires list(hd, len) &*& len > 0;
  //@   ensures hd->next |-> ?tl &*& malloc_block_list_node(hd) &*& list(tl, len-1);
  //@ { open list(hd, len); }
  //@ split_list(last_sorted, n);
  //@ assert list(next0, n-1);
  
  while (last_sorted->next != 0)
  //@ invariant *pfirst |-> ?cur_first &*& list(cur_first, ?len1) &*& last_sorted |-> ?ls_val &*& ls_val != 0 &*& list(ls_val, ?len2) &*& len1 == len2 + ?unsorted_len &*& unsorted_len >= 1;
  {
    struct list_node** pn = pfirst;
    
    int comparison = compare(*pn, last_sorted->next); 
    
    while (pn != &(last_sorted->next) && comparison < 0)
    //@ invariant pn != &(last_sorted->next) ? (*pn |-> ?x &*& list(x, _) &*& x != 0) : true;
    //@ invariant pn != &(last_sorted->next) ? (last_sorted->next |-> ?y &*& list(y, _) &*& y != 0) : true;
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
//@ requires list(l, ?n);
//@ ensures list(result, n);
{
  insertion_sort_core(&l);
  return l;
}