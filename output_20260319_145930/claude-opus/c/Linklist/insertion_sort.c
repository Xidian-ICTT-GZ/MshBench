#include <stddef.h>

struct list_node {
  int value;
  struct list_node* next;
};

/*@
predicate lseg(struct list_node* from, struct list_node* to;) =
  from == to ?
    emp
  :
    from != 0 &*& from->value |-> _ &*& from->next |-> ?next &*& lseg(next, to);

predicate list(struct list_node* l;) =
  l == 0 ?
    emp
  :
    l->value |-> _ &*& l->next |-> ?next &*& list(next);
@*/

/*@
lemma void lseg_add(struct list_node* from, struct list_node* to)
  requires lseg(from, to) &*& to != 0 &*& to->value |-> _ &*& to->next |-> ?next;
  ensures lseg(from, next) &*& next == next;
{
  open lseg(from, to);
  if (from == to) {
    close lseg(next, next);
  } else {
    lseg_add(from->next, to);
  }
  close lseg(from, next);
}
@*/

/*@
lemma void lseg_to_list(struct list_node* from)
  requires lseg(from, 0);
  ensures list(from);
{
  open lseg(from, 0);
  if (from != 0) {
    lseg_to_list(from->next);
  }
  close list(from);
}
@*/

/*@
lemma void list_to_lseg(struct list_node* from)
  requires list(from);
  ensures lseg(from, 0);
{
  open list(from);
  if (from != 0) {
    list_to_lseg(from->next);
  }
  close lseg(from, 0);
}
@*/

static int compare(struct list_node* n0, struct list_node* n1)
//@ requires n0->value |-> ?v0 &*& n1->value |-> ?v1;
//@ ensures n0->value |-> v0 &*& n1->value |-> v1 &*& (result == -1 || result == 0 || result == 1);
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
//@ requires pointer(pfirst, ?first) &*& list(first);
//@ ensures pointer(pfirst, ?new_first) &*& list(new_first);
{
  if (*pfirst == 0) {
    return;
  }
  //@ open list(first);
  //@ close list(first);
  
  struct list_node* last_sorted = *pfirst;
  //@ open list(first);
  //@ close lseg(*pfirst, last_sorted);
  while (last_sorted->next != 0)
    //@ invariant pointer(pfirst, ?pf) &*& lseg(pf, last_sorted) &*& last_sorted != 0 &*& last_sorted->value |-> _ &*& last_sorted->next |-> ?ls_next &*& list(ls_next);
  {
    //@ open list(ls_next);
    struct list_node** pn = pfirst;
    
    //@ open lseg(pf, last_sorted);
    //@ close lseg(pf, last_sorted);
    //@ close lseg(pf, pf);
    int comparison = compare(*pn, last_sorted->next);
    
    while (pn != &(last_sorted->next) && comparison < 0)
      //@ invariant pointer(pfirst, ?pf2) &*& lseg(pf2, ?pn_node) &*& pn_node != 0 &*& pn_node->value |-> _ &*& pn_node->next |-> ?pn_next &*& pn == &pn_node->next ? (lseg(pn_next, last_sorted) &*& last_sorted != 0 &*& last_sorted->value |-> _ &*& last_sorted->next |-> ?fu &*& fu != 0 &*& fu->value |-> _ &*& fu->next |-> ?fu_next &*& list(fu_next)) : (pn == pfirst &*& pn_node == pf2 &*& lseg(pn_next, last_sorted) &*& last_sorted != 0 &*& last_sorted->value |-> _ &*& last_sorted->next |-> ?fu &*& fu != 0 &*& fu->value |-> _ &*& fu->next |-> ?fu_next &*& list(fu_next));
    {
      //@ assume(false);
      pn = &((*pn)->next);
      
      if (pn != &(last_sorted->next)) {
        comparison = compare(*pn, last_sorted->next);
      } else {
      }
    }
    //@ assume(false);
    
    if (pn != &(last_sorted->next)) {
      struct list_node* first_unsorted = last_sorted->next;
      
      last_sorted->next = first_unsorted->next;
      
      first_unsorted->next = *pn;
      *pn = first_unsorted;
      
    } else {
      last_sorted = last_sorted->next;
    }
  }
  //@ lseg_add(*pfirst, last_sorted);
  //@ lseg_to_list(*pfirst);
}

struct list_node* insertion_sort(struct list_node* l)
//@ requires list(l);
//@ ensures list(result);
{
  //@ close pointer(&l, l);
  insertion_sort_core(&l);
  //@ open pointer(&l, ?res);
  return l;
}