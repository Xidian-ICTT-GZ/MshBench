/*@ predicate list(struct list_node* p; int length) =
    p == 0 ?
        length == 0
    :
        length > 0 &*&
        malloc_block_list_node(p) &*&
        list(p->next, length - 1);
@*/

/*@ lemma void list_split(struct list_node* p, int n)
    requires list(p, ?m) &*& 0 <= n &*& n <= m;
    ensures
        list(p, n) &*&
        (n == m ? true : p != 0 &*& list(p + n, m - n));
@*/

/*@ lemma void list_join(struct list_node* p, int n)
    requires
        list(p, n) &*&
        (n == ?m ? true : p != 0 &*& list(p + n, ?k));
    ensures list(p, n + k);
@*/

//@ requires [?f]list(?p, ?n);
//@ ensures [f]list(p, n);
void insertion_sort_core(struct list_node** pfirst)
{
  if (*pfirst == 0) {
    return;
  }  
  
  struct list_node* last_sorted = *pfirst;
  //@ open list(last_sorted, _);
  //@ assert malloc_block_list_node(last_sorted);
  while (last_sorted->next != 0)
  //@ invariant
  
  
  
  
  
  
  
  
  
  {
    struct list_node** pn = pfirst;
    //@ open list(*pn, _);
    //@ assert malloc_block_list_node(*pn);
    int comparison = compare(*pn, last_sorted->next); 
    
    while (pn != &(last_sorted->next) && comparison < 0)
    //@ invariant
    
    
    
    
    
    
    
    
    
    
    
    
    
    
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

//@ requires [?f]list(?l, ?n);
//@ ensures [f]list(result, n);
struct list_node* insertion_sort(struct list_node* l)
{
  insertion_sort_core(&l);
  return l;
}

//@ requires [?f]malloc_block_list_node(n0) &*& [?g]malloc_block_list_node(n1);
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