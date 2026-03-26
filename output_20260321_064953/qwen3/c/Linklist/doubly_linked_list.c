//@ #include "library/list.gh"

/*@
predicate nodep(node n; int item, node next, node prev) =
  n != 0 ?
    malloc_block_node(n) &*&
    n->item |-> item &*&
    n->next |-> next &*&
    n->prev |-> prev
  : false;

predicate nodes(node n; list<int> items, node next, node prev) =
  switch(items) {
    case nil: return n == 0;
    case cons(h, t): return
      nodep(n, h, ?n1, prev) &*&
      nodes(n1, t, next, n);
  };

predicate dllistp(dllist l; list<int> items) =
  malloc_block_dllist(l) &*&
  l->head |-> ?h &*&
  l->tail |-> ?t &*&
  (items == nil ?
    h == 0 &*& t == 0
  :
    nodes(h, items, 0, 0) &*&
    t == last_node(h)
  );
@*/

void reverse(dllist arg)
//@ requires dllistp(arg, ?items);
//@ ensures dllistp(arg, reverse(items));
{
//@ open dllistp(arg, items);
  node ptr = arg->head;
  node temp1 = 0;
  node temp2 = 0;
  
//@ if (items != nil) open nodes(ptr, items, 0, 0);
  while (ptr != 0)
    //@ invariant ptr != 0 ? nodes(ptr, ?rest, ?orig_next, ?orig_prev) : true;
    //@ invariant ptr == 0 ? items == nil : items == ?prefix ++ rest;
    //@ invariant temp1 == 0 &*& temp2 == 0;
  {
    temp1 = ptr->next;
    temp2 = ptr->prev;
    ptr->next = temp2;
    ptr->prev = temp1;
    
//@ open nodep(ptr, _, _, _);
//@ close nodep(ptr, _, temp2, temp1);
    ptr = temp1;
  }
  
  temp1 = arg->head;
  temp2 = arg->tail;
  arg->head = temp2;
  arg->tail = temp1;
//@ close dllistp(arg, reverse(items));
}