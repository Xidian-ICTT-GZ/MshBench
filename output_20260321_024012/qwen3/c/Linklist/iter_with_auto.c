/*@ 
predicate node(struct node *n; struct node *next, int value) =
  n != 0 &*&
  struct_node_next(n, next) &*&
  struct_node_value(n, value);
  
predicate llist(struct llist *l; struct node *first, struct node *last) =
  l != 0 &*&
  struct_llist_first(l, first) &*&
  struct_llist_last(l, last);

predicate iter(struct iter *i; struct node *current) =
  i != 0 &*&
  struct_iter_current(i, current);
@*/

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
//@ ensures llist(result, ?first, ?last) &*& node(first, 0, 0) &*& first == last;
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
//@ requires llist(list, ?first, ?last) &*& node(last, 0, ?old_val);
//@ ensures llist(list, first, ?new_last) &*& node(last, new_last, x) &*& node(new_last, 0, 0);
{
  struct node *l = 0;
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) {
    abort();
  }
  //@ close node(n, 0, 0);
  l = list->last;
  //@ open node(l, _, _);
  l->next = n;
  l->value = x;
  //@ close node(l, n, x);
  list->last = n;
  //@ open llist(list, _, _);
  //@ close llist(list, first, n);
}

void llist_append(struct llist *list1, struct llist *list2)
//@ requires llist(list1, ?f1, ?l1) &*& llist(list2, ?f2, ?l2) &*& node(f2, ?n2, ?v2) &*& (n2 == 0 ? f2 == l2 : true);
//@ ensures llist(list1, f1, l2) &*& (n2 == 0 ? true : node(l1, n2, v2));
{
  struct node *l1 = list1->last;
  struct node *f2 = list2->first;
  struct node *l2 = list2->last;
  
  //@ open llist(list1, _, _);
  //@ open llist(list2, _, _);
  //@ open node(f2, ?next_f2, ?val_f2);
  
  if (f2 == l2) {
    
    free(l2);
    free(list2);
  } else {
    
    l1->next = f2->next;
    l1->value = f2->value;
    list1->last = l2;
    
    free(f2);
    free(list2);
    //@ close node(l1, next_f2, val_f2);
  }
  //@ close llist(list1, f1, l2);
}

void llist_dispose(struct llist *list)
//@ requires llist(list, ?first, ?last) &*& node(first, ?n, ?v) &*& (n == 0 ? first == last : true);
//@ ensures true;
{
  struct node *n = list->first;
  struct node *l = list->last;
  //@ open llist(list, _, _);
  while (n != l)
  //@ invariant n != l &*& node(n, ?next, ?val) &*& node(l, 0, ?lv);
  {
    struct node *next = n->next;
    //@ open node(n, _, _);
    free(n);
    n = next;
  }
  
  //@ open node(l, _, _);
  free(l);
  free(list);
}

int llist_length(struct llist *list)
//@ requires llist(list, ?first, ?last) &*& node(first, ?n, ?v) &*& (n == 0 ? first == last : true);
//@ ensures llist(list, first, last) &*& node(first, n, v) &*& (n == 0 ? first == last : true) &*& result >= 0;
{
  struct node *f = list->first;
  struct node *n = f;
  struct node *l = list->last;
  int c = 0;
  
  //@ open llist(list, _, _);
  //@ open node(f, ?next_f, ?val_f);
  //@ close node(f, next_f, val_f);
  //@ close llist(list, f, l);
  
  while (n != l)
  //@ invariant n != l &*& node(n, ?next_n, ?val_n) &*& node(l, 0, ?lv) &*& c >= 0;
  {
    struct node *next = n->next;
    //@ open node(n, _, _);
    n = next;
    if (c == INT_MAX) abort();
    c = c + 1;
    //@ close node(n, ?next_next, ?val_next);
  }
  
  return c;
}

int llist_lookup(struct llist *list, int index)
//@ requires llist(list, ?first, ?last) &*& node(first, ?n, ?v) &*& (n == 0 ? first == last : true) &*& index >= 0;
//@ ensures llist(list, first, last) &*& node(first, n, v) &*& (n == 0 ? first == last : true);
{
  struct node *f = list->first;
  struct node *l = list->last;
  struct node *n = f;
  int i = 0;
  //@ open llist(list, _, _);
  //@ open node(f, ?next_f, ?val_f);
  //@ close node(f, next_f, val_f);
  //@ close llist(list, f, l);
  while (i < index)
  //@ invariant i <= index &*& node(n, ?next_n, ?val_n) &*& node(l, 0, ?lv);
  {
    struct node *next = n->next;
    //@ open node(n, _, _);
    n = next;
    i = i + 1;
    //@ close node(n, ?next_next, ?val_next);
  }
  
  int value = n->value;
  return value;
}

int llist_removeFirst(struct llist *l)
//@ requires llist(l, ?first, ?last) &*& node(first, ?next_first, ?val_first) &*& first != last;
//@ ensures llist(l, next_first, last) &*& result == val_first;
{
  struct node *nf = l->first;
  //@ open llist(l, _, _);
  //@ open node(nf, ?nfn, ?nfv);
  struct node *nfn = nf->next;
  int nfv = nf->value;
  free(nf);
  l->first = nfn;
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
  //@ assert x1 == 10;
  int x2 = llist_removeFirst(l);
  //@ assert x2 == 20;
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
  int x = llist_removeFirst(l2); //@ assert x == 40;
  llist_append(l1, l2);
  int n = llist_length(l1); //@ assert n == 5;
  int e0 = llist_lookup(l1, 0); //@ assert e0 == 10;
  int e1 = llist_lookup(l1, 1); //@ assert e1 == 20;
  int e2 = llist_lookup(l1, 2); //@ assert e2 == 30;
  int e3 = llist_lookup(l1, 3); //@ assert e3 == 50;
  int e4 = llist_lookup(l1, 4); //@ assert e4 == 60;
  llist_dispose(l1);
  return 0;
}

struct iter {
    struct node *current;
};

struct iter *llist_create_iter(struct llist *l)
//@ requires llist(l, ?first, ?last) &*& node(first, ?n, ?v) &*& (n == 0 ? first == last : true);
//@ ensures iter(result, first);
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
//@ requires iter(i, ?current) &*& node(current, ?next, ?val);
//@ ensures iter(i, next) &*& result == val;
{
    struct node *c = i->current;
    //@ open iter(i, _);
    //@ open node(c, ?n, ?v);
    int value = c->value;
    struct node *n = c->next;
    i->current = n;
    //@ close iter(i, n);
    return value;
}

void iter_dispose(struct iter *i)
//@ requires iter(i, ?current);
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
    int i1e1 = iter_next(i1); //@ assert i1e1 == 5;
    int i2e1 = iter_next(i2); //@ assert i2e1 == 5;
    int i1e2 = iter_next(i1); //@ assert i1e2 == 10;
    int i2e2 = iter_next(i2); //@ assert i2e2 == 10;
    iter_dispose(i1);
    iter_dispose(i2);
    llist_dispose(l);
    return 0;
}