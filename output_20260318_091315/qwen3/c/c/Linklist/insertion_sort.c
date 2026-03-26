/*@ predicate list(struct list_node* p; int length) =
    p == 0 ?
        length == 0
    :
        malloc_block_list_node(p) &*&
        list(p->next, length - 1);
@*/

/*@ lemma void list_split(struct list_node* p, int n)
    requires list(p, ?m) &*& 0 <= n &*& n <= m;
    ensures list(p, n) &*& list(?q, m - n) &*& n == 0 ? p == 0 : (n == m ? q == 0 : true);
@*/
{
    if (p == 0) {
    } else {
        list_split(p->next, n - 1);
    }
}

/*@ lemma void list_join(struct list_node* p, struct list_node* q, int n, int m)
    requires list(p, n) &*& list(q, m) &*& (n == 0 ? p == 0 : true) &*& (n > 0 ? p->next == q : true);
    ensures list(p, n + m);
@*/
{
    if (p == 0) {
    } else {
        list_join(p->next, q, n - 1, m);
    }
}

static int compare(struct list_node* n0, struct list_node* n1)
//@ requires malloc_block_list_node(n0) &*& malloc_block_list_node(n1);
//@ ensures malloc_block_list_node(n0) &*& malloc_block_list_node(n1) &*& result == -1 || result == 0 || result == 1;
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
//@ ensures *pfirst |-> ?sorted &*& list(sorted, n) &*& sorted == 0 || (list(?rest, n - 1) &*& sorted->next == rest);
{
  if (*pfirst == 0) {
    return;
  }  
  
  struct list_node* last_sorted = *pfirst;
  //@ open list(last_sorted, n);
  //@ assert malloc_block_list_node(last_sorted) &*& list(last_sorted->next, n - 1);
  while (last_sorted->next != 0)
  //@ invariant *pfirst |-> ?head &*& list(head, ?k) &*& last_sorted != 0 &*& list(last_sorted->next, ?m) &*& k == (n - m);
  {
    struct list_node** pn = pfirst;
    //@ open list(*pn, k);
    //@ assert malloc_block_list_node(*pn) &*& list((*pn)->next, k - 1);
    
    int comparison = compare(*pn, last_sorted->next); 
    
    while (pn != &(last_sorted->next) && comparison < 0)
    //@ invariant pn != &(last_sorted->next) ? (*pn != last_sorted->next) : true &*& *pn |-> ?curr &*& malloc_block_list_node(curr) &*& list(curr->next, ?r) &*& list(last_sorted->next, m) &*& pn != pfirst ? true : (*pfirst |-> curr) &*& pn == &((?prev)->next) ? (malloc_block_list_node(prev) &*& prev->next == curr) : (pn == pfirst);
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