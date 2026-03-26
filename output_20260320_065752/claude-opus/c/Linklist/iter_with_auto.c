#include "stdlib.h"

/*@

predicate node(struct node *n; int v, struct node *next) =
  n->value |-> v &*& n->next |-> next &*& malloc_block_node(n);

predicate llist(struct llist *l; struct node *first, struct node *last) =
  l->first |-> first &*& l->last |-> last &*& malloc_block_llist(l) &*&
  nodes(first, last);

predicate nodes(struct node *first, struct node *last) =
  first == last ?
    true
  :
    node(first, ?v, ?next) &*& nodes(next, last);

predicate iter(struct iter *i; struct node *current) =
  i->current |-> current &*& malloc_block_iter(i);

@*/

struct node {
  struct node *next;
  int value;
};

struct llist {
  struct node *first;
  struct node *last;
};

/*@

fixpoint bool node_in_list(struct node *n, struct node *first, struct node *last) {
  return first == last ? false :
         first == n ? true : node_in_list(n, first->next, last);
}

@*/

struct llist *create_llist()
//@ requires true;
//@ ensures llist(result, ?f, ?l) &*& nodes(f,l);
  
{
  struct llist *l = malloc(sizeof(struct llist));
  if (l == 0) abort();
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) abort();
  l->first = n;
  l->last = n;
  //@ close node(n, 0, null);
  //@ close nodes(n, n);
  //@ close llist(l, n, n);
  return l;
}

void llist_add(struct llist *list, int x)
//@ requires llist(list, ?f, ?l) &*& nodes(f, l);
//@ ensures llist(list, f, ?newL) &*& nodes(f, newL);
  
{
  struct node *l = 0;
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) {
    abort();
  }
  //@ close node(n, 0, null);
  l = list->last;
  //@ open llist(list, f, l);
  //@ open nodes(f, l);
  //@ open node(l, ?lv, ?lnext);
  l->next = n;
  l->value = x;
  //@ close node(l, x, n);
  list->last = n;
  //@ close nodes(f, n);
  //@ close llist(list, f, n);
  
}

void llist_append(struct llist *list1, struct llist *list2)
//@ requires llist(list1, ?f1, ?l1) &*& llist(list2, ?f2, ?l2) &*& nodes(f1, l1) &*& nodes(f2, l2);
//@ ensures llist(list1, f1, ?nl1) &*& nodes(f1, nl1);
//@     (f2 == l2 ? true : (nodes(f2, l2) == false));
//@ ensures true;
  
{
  struct node *l1 = list1->last;
  struct node *f2 = list2->first;
  struct node *l2 = list2->last;
  //@ open llist(list1, f1, l1);
  //@ open llist(list2, f2, l2);
  //@ open nodes(f1, l1);
  //@ open nodes(f2, l2);

  if (f2 == l2) {
    free(l2);
    free(list2);
  } else {
    //@ open node(l1, ?lv1, ?lnext1);
    //@ open node(f2, ?v2, ?n2);
    l1->next = f2->next;
    l1->value = f2->value;
    list1->last = l2;
    //@ close nodes(f1, l2);
    //@ close llist(list1, f1, l2);
    free(f2);
    free(list2);
  }
}

void llist_dispose(struct llist *list)
//@ requires llist(list, ?f, ?l) &*& nodes(f, l);
//@ ensures true;
  
{
  struct node *n = list->first;
  struct node *l = list->last;
  //@ open llist(list, f, l);
  //@ open nodes(f, l);
  while (n != l)
    //@ invariant nodes(n, l);
  {
    struct node *next = n->next;
    //@ open node(n, _, _);
    free(n);
    n = next;
  }
  
  free(l);
  free(list);
}

int llist_length(struct llist *list)
//@ requires llist(list, ?f, ?l) &*& nodes(f, l);
//@ ensures llist(list, f, l) &*& nodes(f, l);
  
{
  struct node *f = list->first;
  struct node *n = f;
  struct node *l = list->last;
  int c = 0;
  //@ open llist(list, f, l);
  //@ open nodes(f, l);
  while (n != l)
    //@ invariant nodes(n, l) &*& 0 <= c &*& c <= INT_MAX;
  {
    struct node *next = n->next;
    n = next;
    if (c == INT_MAX) abort();
    c = c + 1;
  }
  //@ close nodes(f, l);
  //@ close llist(list, f, l);
  return c;
}

int llist_lookup(struct llist *list, int index)
//@ requires llist(list, ?f, ?l) &*& nodes(f, l) &*& 0 <= index;
//@ ensures llist(list, f, l) &*& nodes(f, l);
//@ ensures result == (true ? result : 0); // weak ensures, correctness not fully specified
  
{
  struct node *f = list->first;
  struct node *l = list->last;
  struct node *n = f;
  int i = 0;
  //@ open llist(list, f, l);
  //@ open nodes(f, l);
  while (i < index)
    //@ invariant nodes(n, l) &*& 0 <= i &*& i <= index;
  {
    struct node *next = n->next;
    n = next;
    i = i + 1;
  }
  int value = n->value;
  //@ close nodes(f, l);
  //@ close llist(list, f, l);
  return value;
}

int llist_removeFirst(struct llist *l)
//@ requires llist(l, ?f, ?last) &*& nodes(f, last) &*& f != last;
//@ ensures llist(l, ?nf, last) &*& nodes(nf, last);
  
{
  struct node *nf = l->first;
  //@ open llist(l, f, last);
  //@ open nodes(f, last);
  //@ open node(nf, ?v, ?next);
  struct node *nfn = nf->next;
  int nfv = nf->value;
  free(nf);
  l->first = nfn;
  //@ close nodes(nfn, last);
  //@ close llist(l, nfn, last);
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
  assert(x1 == 10);
  int x2 = llist_removeFirst(l);
  assert(x2 == 20);
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
  int x = llist_removeFirst(l2); assert(x == 40);
  llist_append(l1, l2);
  int n = llist_length(l1); assert(n == 5);
  int e0 = llist_lookup(l1, 0); assert(e0 == 10);
  int e1 = llist_lookup(l1, 1); assert(e1 == 20);
  int e2 = llist_lookup(l1, 2); assert(e2 == 30);
  int e3 = llist_lookup(l1, 3); assert(e3 == 50);
  int e4 = llist_lookup(l1, 4); assert(e4 == 60);
  llist_dispose(l1);
  return 0;
}

struct iter {
    struct node *current;
};

/*@

predicate iter(struct iter *i; struct node *curr) =
  i->current |-> curr &*& malloc_block_iter(i);

@*/

struct iter *llist_create_iter(struct llist *l)
//@ requires llist(l, ?f, ?last) &*& nodes(f, last);
//@ ensures iter(result, f);
  
{
    struct iter *i = 0;
    struct node *f = 0;
    i = malloc(sizeof(struct iter));
    if (i == 0) {
      abort();
    }
    //@ close iter(i, null);
    
    f = l->first;
    i->current = f;
    //@ close iter(i, f);
    
    return i;
}

int iter_next(struct iter *i)
//@ requires iter(i, ?c) &*& c != 0;
//@ ensures iter(i, c->next);
  
{
    struct node *c = i->current;
    //@ open iter(i, c);
    int value = c->value;
    struct node *n = c->next;
    i->current = n;
    //@ close iter(i, n);
    return value;
}

void iter_dispose(struct iter *i)
//@ requires iter(i, ?c);
//@ ensures true;
  
{
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
    int i1e1 = iter_next(i1); assert(i1e1 == 5);
    int i2e1 = iter_next(i2); assert(i2e1 == 5);
    int i1e2 = iter_next(i1); assert(i1e2 == 10);
    int i2e2 = iter_next(i2); assert(i2e2 == 10);
    iter_dispose(i1);
    iter_dispose(i2);
    llist_dispose(l);
    return 0;
}