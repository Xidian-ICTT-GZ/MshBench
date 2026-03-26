/*@ 
predicate list(struct list_node* node) =
  node == 0 ?
    true
  :
    malloc_block_list_node(node) &*& list(node->next);
@*/

//@ requires [?f]list(?l);
//@ ensures [f]list(result);
struct list_node* insertion_sort(struct list_node* l)
{
  insertion_sort_core(&l);
  return l;
}

//@ requires pfirst != 0 &*& *pfirst |-> ?first &*& [?f]list(first);
//@ ensures *pfirst |-> ?result &*& [f]list(result);
void insertion_sort_core(struct list_node** pfirst)
{
  if (*pfirst == 0) {
    
    return;
  }  
  
  struct list_node* last_sorted = *pfirst;
  //@ open list(last_sorted);
  while (last_sorted->next != 0)
  {
    //@ open list(last_sorted->next);
    struct list_node** pn = pfirst;
    
    int comparison = compare(*pn, last_sorted->next); 
    
    while (pn != &(last_sorted->next) && comparison < 0)
    { 
      //@ open list(*pn);
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
      
      //@ close list(first_unsorted);
    } else {
      last_sorted = last_sorted->next;
      //@ close list(last_sorted);
    }
    //@ close list(last_sorted);
  }
  //@ close list(*pfirst);
}

//@ requires n0 != 0 &*& n1 != 0 &*& malloc_block_list_node(n0) &*& malloc_block_list_node(n1);
//@ ensures true;
static int compare(struct list_node* n0, struct list_node* n1)
{
  if (n0->value < n1->value) {
    return -1;
  } else if (n0->value > n1->value) {
    return 1;
  } else {
    return 0;
  }
}