/*@ predicate node(struct node *n; struct node *next, int value) = n != 0 &*& n->next |-> next &*& n->value |-> value; @*/
/*@ predicate llist(struct llist *l; struct node *first, struct node *last) = l != 0 &*& l->first |-> first &*& l->last |-> last; @*/
/*@ predicate iter(struct iter *i; struct node *current) = i != 0 &*& i->current |-> current; @*/

#include "stdlib.h"

struct node {
  struct node *next;
  int value;
};

struct llist {
  struct node *first;
  struct node *last;
};

struct llist *create_llist()
//@ requires true;
//@ ensures llist(result, ?f, ?l) &*& node(f, 0, 0) &*& f == l;
{
  struct llist *l = malloc(sizeof(struct llist));
  if (l == 0) abort();
  //@ close llist(l, 0, 0);
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) abort();
  //@ close node(n, 0, 0);
  l->first = n;
  l->last = n;
  //@ open llist(l, _, _);
  //@ close llist(l, n, n);
  return l;
}

void llist_add(struct llist *list, int x)
//@ requires llist(list, ?first, ?last) &*& node(last, 0, _) &*& malloc_block_node(last);
//@ ensures llist(list, first, ?new_last) &*& node(last, new_last, x) &*& node(new_last, 0, 0) &*& malloc_block_node(new_last);
{
  struct node *l = 0;
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) {
    abort();
  }
  //@ close node(n, 0, 0);
  l = list->last;
  //@ open llist(list, _, _);
  l->next = n;
  l->value = x;
  list->last = n;
  //@ close llist(list, _, n);
}

void llist_append(struct llist *list1, struct llist *list2)
//@ requires llist(list1, ?f1, ?l1) &*& node(l1, 0, _) &*& malloc_block_node(l1) &*&
//@          llist(list2, ?f2, ?l2) &*& node(f2, ?f2_next, ?f2_val) &*& 
//@          (f2 == l2 ? 
//@             malloc_block_node(f2) &*& f2_next == 0
//@           : 
//@             malloc_block_node(f2) &*& node(l2, 0, _) &*& malloc_block_node(l2));
//@ ensures llist(list1, f1, l2) &*& 
//@         (f2 == l2 ? 
//@            true
//@          : 
//@            node(l1, f2_next, f2_val) &*& node(l2, 0, _) &*& malloc_block_node(l2)) &*&
//@         malloc_block_llist(list2);
{
  struct node *l1 = list1->last;
  struct node *f2 = list2->first;
  struct node *l2 = list2->last;
  
  //@ open llist(list1, _, _);
  //@ open llist(list2, _, _);
  if (f2 == l2) {
    //@ open node(f2, _, _);
    free(l2);
    free(list2);
    
  } else {
    //@ open node(f2, ?f2n, ?f2v);
    l1->next = f2->next;
    l1->value = f2->value;
    list1->last = l2;
    //@ close node(l1, f2n, f2v);
    //@ close llist(list1, _, l2);
    free(f2);
    free(list2);
  }
}

void llist_dispose(struct llist *list)
//@ requires llist(list, ?first, ?last) &*& node(first, ?n, ?v) &*& 
//@          (first == last ? 
//@             n == 0 &*& malloc_block_node(first)
//@           : 
//@             malloc_block_node(first) &*& 
//@             llist_nodes(n, last));
//@ ensures true;
{
  
  struct node *n = list->first;
  struct node *l = list->last;
  //@ open llist(list, _, _);
  while (n != l)
  //@ invariant n != l &*& node(n, ?next, ?val) &*& malloc_block_node(n) &*& llist_nodes(next, l);
  {
    struct node *next = n->next;
    free(n);
    n = next;
  }
  //@ assert n == l;
  //@ open node(n, _, _);
  free(l);
  free(list);
}

/*@ predicate llist_nodes(struct node *first, struct node *last;) =
    first == last ?
      node(first, 0, _) &*& malloc_block_node(first)
    :
      node(first, ?next, _) &*& malloc_block_node(first) &*& llist_nodes(next, last);
@*/

int llist_length(struct llist *list)
//@ requires llist(list, ?first, ?last) &*& node(first, ?n, ?v) &*& 
//@          (first == last ? 
//@             n == 0 &*& malloc_block_node(first)
//@           : 
//@             malloc_block_node(first) &*& llist_nodes(n, last));
//@ ensures llist(list, first, last) &*& node(first, n, v) &*& 
//@         (first == last ? 
//@            n == 0 &*& malloc_block_node(first)
//@          : 
//@            malloc_block_node(first) &*& llist_nodes(n, last)) &*&
//@         result >= 0;
{
  struct node *f = list->first;
  struct node *n = f;
  struct node *l = list->last;
  int c = 0;
  
  while (n != l)
  //@ invariant n != l &*& node(n, ?next, ?val) &*& malloc_block_node(n) &*& llist_nodes(next, l) &*& c >= 0;
  {
    struct node *next = n->next;
    n = next;
    if (c == INT_MAX) abort();
    c = c + 1;
  }
  return c;
}

int llist_lookup(struct llist *list, int index)
//@ requires llist(list, ?first, ?last) &*& node(first, ?n, ?v) &*& 
//@          (first == last ? 
//@             n == 0 &*& malloc_block_node(first)
//@           : 
//@             malloc_block_node(first) &*& llist_nodes(n, last)) &*&
//@          index >= 0 &*& index < llist_length_(list);
//@ ensures llist(list, first, last) &*& node(first, n, v) &*& 
//@         (first == last ? 
//@            n == 0 &*& malloc_block_node(first)
//@          : 
//@            malloc_block_node(first) &*& llist_nodes(n, last)) &*&
//@         result == nth_value_(list, index);
{
  struct node *f = list->first;
  struct node *l = list->last;
  struct node *n = f;
  int i = 0;
  
  while (i < index)
  //@ invariant i <= index &*& n != l &*& node(n, ?next, ?val) &*& malloc_block_node(n) &*& llist_nodes(next, l);
  {
    struct node *next = n->next;
    n = next;
    i = i + 1;
  }
  int value = n->value;
  return value;
}

/*@ fixpoint int llist_length_(struct llist *l;) { return 0; } @*/
/*@ fixpoint int nth_value_(struct llist *l, int i;) { return 0; } @*/

int llist_removeFirst(struct llist *l)
//@ requires llist(l, ?first, ?last) &*& node(first, ?next, ?val) &*& malloc_block_node(first) &*& first != last;
//@ ensures llist(l, next, last) &*& node(next, ?nnext, ?nval) &*& malloc_block_node(next) &*& result == val;
{
  struct node *nf = l->first;
  //@ open llist(l, _, _);
  //@ open node(nf, ?nfn, ?nfv);
  struct node *nfn = nf->next;
  int nfv = nf->value;
  free(nf);
  l->first = nfn;
  //@ close llist(l, nfn, _);
  return nfv;
}

void main0()
//@ requires true;
//@ ensures true;
{
  struct llist *l = create_llist();
  llist_add(l, 10);
  llist_add(l, 20);
  llist_add(l, 30);
  llist_add(l, 40);
  int x1 = llist_removeFirst(l);
  //@ assert(x1 == 10);
  int x2 = llist_removeFirst(l);
  //@ assert(x2 == 20);
  llist_dispose(l);
}

int main() 
//@ requires true;
//@ ensures true;
{
  struct llist *l1 = create_llist();
  struct llist *l2 = create_llist();
  llist_add(l1, 10);
  llist_add(l1, 20);
  llist_add(l1, 30);
  llist_add(l2, 40);
  llist_add(l2, 50);
  llist_add(l2, 60);
  int x = llist_removeFirst(l2); //@ assert(x == 40);
  llist_append(l1, l2);
  int n = llist_length(l1); //@ assert(n == 5);
  int e0 = llist_lookup(l1, 0); //@ assert(e0 == 10);
  int e1 = llist_lookup(l1, 1); //@ assert(e1 == 20);
  int e2 = llist_lookup(l1, 2); //@ assert(e2 == 30);
  int e3 = llist_lookup(l1, 3); //@ assert(e3 == 50);
  int e4 = llist_lookup(l1, 4); //@ assert(e4 == 60);
  llist_dispose(l1);
  return 0;
}

struct iter {
    struct node *current;
};

struct iter *llist_create_iter(struct llist *l)
//@ requires llist(l, ?first, ?last) &*& node(first, ?n, ?v) &*& 
//@          (first == last ? 
//@             n == 0 &*& malloc_block_node(first)
//@           : 
//@             malloc_block_node(first) &*& llist_nodes(n, last));
//@ ensures iter(result, first) &*& llist(l, first, last) &*& node(first, n, v) &*& 
//@         (first == last ? 
//@            n == 0 &*& malloc_block_node(first)
//@          : 
//@            malloc_block_node(first) &*& llist_nodes(n, last));
{
    struct iter *i = 0;
    struct node *f = 0;
    
    i = malloc(sizeof(struct iter));
    if (i == 0) {
      abort();
    }
    //@ close iter(i, 0);
    f = l->first;
    i->current = f;
    //@ open iter(i, _);
    //@ close iter(i, f);
    return i;
}

int iter_next(struct iter *i)
//@ requires iter(i, ?c) &*& node(c, ?next, ?val) &*& malloc_block_node(c);
//@ ensures iter(i, next) &*& node(c, next, val) &*& malloc_block_node(c) &*& result == val;
{
    struct node *c = i->current;
    //@ open iter(i, _);
    int value = c->value;
    struct node *n = c->next;
    i->current = n;
    //@ close iter(i, n);
    return value;
}

void iter_dispose(struct iter *i)
//@ requires iter(i, _);
//@ ensures true;
{
    //@ open iter(i, _);
    free(i);
}

int main2()
//@ requires true;
//@ ensures true;
{
    struct llist *l = create_llist();
    llist_add(l, 5);
    llist_add(l, 10);
    llist_add(l, 15);
    struct iter *i1 = llist_create_iter(l);
    struct iter *i2 = llist_create_iter(l);
    int i1e1 = iter_next(i1); //@ assert(i1e1 == 5);
    int i2e1 = iter_next(i2); //@ assert(i2e1 == 5);
    int i1e2 = iter_next(i1); //@ assert(i1e2 == 10);
    int i2e2 = iter_next(i2); //@ assert(i2e2 == 10);
    iter_dispose(i1);
    iter_dispose(i2);
    llist_dispose(l);
    return 0;
}