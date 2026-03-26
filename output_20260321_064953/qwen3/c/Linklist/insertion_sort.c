//@ #include "library/alloc.gh"

/*@ 
predicate list(struct list_node* node; list<int> vs) =
  node == 0 ?
    vs == nil
  :
    malloc_block_list_node(node) &*&
    node->value |-> ?v &*&
    node->next |-> ?next &*&
    list(next, ?tail) &*&
    vs == cons(v, tail);
@*/

static int compare(struct list_node* n0, struct list_node* n1)
//@ requires list(n0, ?vs0) &*& list(n1, ?vs1);
//@ ensures list(n0, vs0) &*& list(n1, vs1);
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
//@ requires *pfirst |-> ?first &*& list(first, ?vs);
//@ ensures *pfirst |-> ?sorted &*& list(sorted, ?sorted_vs) &*& permutation(vs, sorted_vs);
{
  if (*pfirst == 0) {
    //@ close list(0, nil);
    return;
  }  
  
  struct list_node* last_sorted = *pfirst;
  //@ open list(last_sorted, _);
  //@ assert malloc_block_list_node(last_sorted) &*& last_sorted->value |-> _ &*& last_sorted->next |-> ?next0;
  while (last_sorted->next != 0)
  //@ invariant *pfirst |-> ?cur_first &*& list(cur_first, ?cur_vs) &*& malloc_block_list_node(last_sorted) &*& last_sorted->next |-> ?ln_next &*& ln_next != 0 &*& list(ln_next, ?rest) &*& append(?prefix, cons(?v, rest), cur_vs) == true;
  {
    struct list_node** pn = pfirst;
    //@ open list(*pn, _);
    //@ assert malloc_block_list_node(*pn) &*& (*pn)->value |-> ?v0 &*& (*pn)->next |-> ?next1;
    
    int comparison = compare(*pn, last_sorted->next); 
    
    while (pn != &(last_sorted->next) && comparison < 0)
    //@ invariant *pfirst |-> ?cur_first2 &*& list(cur_first2, ?cur_vs2) &*& pn |-> ?pn_val &*& *pn_val |-> ?node &*& list(node, ?suffix) &*& pn != &(last_sorted->next) &*& malloc_block_list_node(last_sorted) &*& last_sorted->next |-> ?ln_next2 &*& ln_next2 != 0 &*& list(ln_next2, ?rest2) &*& append(?prefix2, cons(?v2, rest2), cur_vs2) == true;
    { 
      pn = &((*pn)->next);
      
      if (pn != &(last_sorted->next)) {
        //@ open list(*pn, _);
        //@ assert malloc_block_list_node(*pn) &*& (*pn)->value |-> ?v3 &*& (*pn)->next |-> ?next2;
        comparison = compare(*pn, last_sorted->next);
      } else {
      }
    }
    
    if (pn != &(last_sorted->next)) {
      struct list_node* first_unsorted = last_sorted->next;
      
      last_sorted->next = first_unsorted->next;
      
      first_unsorted->next = *pn;
      *pn = first_unsorted;
      
      //@ close list(first_unsorted, _);
    } else {
      last_sorted = last_sorted->next;
      //@ open list(last_sorted, _);
    }
  }
}

struct list_node* insertion_sort(struct list_node* l)
//@ requires list(l, ?vs);
//@ ensures list(result, ?sorted_vs) &*& permutation(vs, sorted_vs);
{
  insertion_sort_core(&l);
  return l;
}