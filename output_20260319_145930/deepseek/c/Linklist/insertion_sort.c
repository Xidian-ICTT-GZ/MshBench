#include <stdlib.h>

struct list_node {
  int value;
  struct list_node* next;
};

/*@
predicate list(struct list_node* n) =
  n == 0 ? true : n->value |-> _ &*& n->next |-> ?next &*& list(next);
@*/

/*@
predicate list_seg(struct list_node* from, struct list_node* to) =
  from == to ? true :
  from->value |-> _ &*& from->next |-> ?next &*& list_seg(next, to);
@*/

/*@
predicate list_with_hole(struct list_node* first, struct list_node** pn, struct list_node* last_sorted) =
  pn == &first ?
    list_seg(first, last_sorted) &*& last_sorted->next |-> ?rest &*& list(rest)
  :
    list_seg(first, *pn) &*& (*pn)->value |-> _ &*& (*pn)->next |-> ?next &*&
    list_seg(next, last_sorted) &*& last_sorted->next |-> ?rest &*& list(rest);
@*/

static int compare(struct list_node* n0, struct list_node* n1)
//@ requires n0->value |-> ?v0 &*& n1->value |-> ?v1;
//@ ensures n0->value |-> v0 &*& n1->value |-> v1 &*& true;
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
  struct list_node* last_sorted = *pfirst;
  //@ close list_seg(last_sorted, last_sorted);
  //@ assert last_sorted->next |-> ?rest0;
  //@ close list(rest0);
  //@ close list_with_hole(first, &first, last_sorted);
  while (last_sorted->next != 0)
  //@ invariant list_with_hole(first, ?pn, last_sorted) &*& pn == &first ? true : *pn |-> ?nval;
  {
    //@ open list_with_hole(first, pn, last_sorted);
    struct list_node** pn = pfirst;
    //@ close list_seg(first, first);
    //@ close list_with_hole(first, pn, last_sorted);
    
    int comparison = compare(*pn, last_sorted->next);
    
    while (pn != &(last_sorted->next) && comparison < 0)
    //@ invariant list_with_hole(first, pn, last_sorted) &*& pn == &first ? true : *pn |-> ?nval_inv;
    {
      pn = &((*pn)->next);
      
      if (pn != &(last_sorted->next)) {
        comparison = compare(*pn, last_sorted->next);
      } else {
        
      }
    }
    
    if (pn != &(last_sorted->next)) {
      struct list_node* first_unsorted = last_sorted->next;
      //@ open list(first_unsorted);
      last_sorted->next = first_unsorted->next;
      
      first_unsorted->next = *pn;
      *pn = first_unsorted;
    } else {
      last_sorted = last_sorted->next;
    }
  }
  //@ open list_with_hole(first, ?final_pn, last_sorted);
  //@ open list_seg(first, last_sorted);
  //@ open list(0);
}

struct list_node* insertion_sort(struct list_node* l)
//@ requires list(l);
//@ ensures list(result);
{
  insertion_sort_core(&l);
  return l;
}