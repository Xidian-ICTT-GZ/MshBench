#include "stdlib.h"

/*@
predicate node_pred(struct node *n) = 
  n != 0 &*& 
  malloc_block_node(n) &*&
  (n->next |-> _) &*&
  (n->value |-> _);
  
predicate llist_pred(struct llist *l) = 
  l != 0 &*& malloc_block_llist(l) &*&
  (l->first |-> ?f) &*& (l->last |-> ?last) &*&
  node_pred(f) &*& node_pred(last);
  
predicate iter_pred(struct iter *i) =
  i != 0 &*& malloc_block_iter(i) &*& i->current |-> ?c &*& (c == 0 || node_pred(c));
@*/

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
  //@ ensures llist_pred(result);
{
  struct llist *l = malloc(sizeof(struct llist));
  if (l == 0) abort();
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) abort();
  l->first = n;
  l->last = n;
  //@ close node_pred(n);
  //@ close llist_pred(l);
  return l;
}

void llist_add(struct llist *list, int x)
  //@ requires llist_pred(list);
  //@ ensures llist_pred(list);
{
  struct node *l = 0;
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) {
    abort();
  }
  //@ close node_pred(n);
  l = list->last;
  //@ open llist_pred(list);
  //@ open node_pred(l);
  l->next = n;
  l->value = x;
  //@ close node_pred(l);
  list->last = n;
  //@ close llist_pred(list);
}

void llist_append(struct llist *list1, struct llist *list2)
  //@ requires llist_pred(list1) &*& llist_pred(list2);
  //@ ensures llist_pred(list1);
{
  //@ open llist_pred(list1);
  struct node *l1 = list1->last;
  //@ open node_pred(l1);
  struct node *f2 = list2->first;
  struct node *l2 = list2->last;
  //@ open llist_pred(list2);
  //@ open node_pred(f2);
  //@ open node_pred(l2);
  
  if (f2 == l2) {
    //@ close node_pred(l2);
    //@ close llist_pred(list2);
    free(l2);
    free(list2);
    //@ close llist_pred(list1);
  } else {
    l1->next = f2->next;
    l1->value = f2->value;
    list1->last = l2;
    //@ close node_pred(l1);
    //@ close node_pred(l2);
    //@ close llist_pred(list1);
    free(f2);
    //@ close llist_pred(list2);
    free(list2);
  }
}

void llist_dispose(struct llist *list)
  //@ requires llist_pred(list);
  //@ ensures true;
{
  //@ open llist_pred(list);
  struct node *n = list->first;
  struct node *l = list->last;
  //@ open node_pred(n);
  //@ open node_pred(l);
  while (n != l)
    //@ invariant node_pred(n) &*& node_pred(l) &*& malloc_block_llist(list);
  {
    struct node *next = n->next;
    free(n);
    n = next;
    if (n != l) {
      //@ open node_pred(n);
    }
  }
  
  free(l);
  free(list);
}

int llist_length(struct llist *list)
  //@ requires llist_pred(list);
  //@ ensures true;
{
  //@ open llist_pred(list);
  struct node *f = list->first;
  struct node *n = f;
  struct node *l = list->last;
  int c = 0;
  //@ open node_pred(f);
  //@ open node_pred(l);
  while (n != l)
    //@ invariant (n != 0) &*& node_pred(n) &*& node_pred(l) &*& malloc_block_llist(list);
  {
    struct node *next = n->next;
    n = next;
    if (c == INT_MAX) abort();
    c = c + 1;
    //@ open node_pred(n);
  }
  //@ close node_pred(l);
  //@ close llist_pred(list);
  return c;
}

int llist_lookup(struct llist *list, int index)
  //@ requires llist_pred(list);
  //@ ensures true;
{
  //@ open llist_pred(list);
  struct node *f = list->first;
  struct node *l = list->last;
  struct node *n = f;
  int i = 0;
  //@ open node_pred(f);
  //@ open node_pred(l);
  while (i < index)
    //@ invariant node_pred(n) &*& node_pred(l) &*& malloc_block_llist(list);
  {
    struct node *next = n->next;
    n = next;
    i = i + 1;
    //@ open node_pred(n);
  }
  int value = n->value;
  //@ close node_pred(n);
  //@ close node_pred(l);
  //@ close llist_pred(list);
  return value;
}

int llist_removeFirst(struct llist *l)
  //@ requires llist_pred(l);
  //@ ensures llist_pred(l);
{
  //@ open llist_pred(l);
  struct node *nf = l->first;
  //@ open node_pred(nf);
  struct node *nfn = nf->next;
  int nfv = nf->value;
  free(nf);
  l->first = nfn;
  //@ open node_pred(nfn);
  //@ close llist_pred(l);
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
predicate malloc_block_iter(struct iter *p) = true; 
@*/

struct iter *llist_create_iter(struct llist *l)
  //@ requires llist_pred(l);
  //@ ensures iter_pred(result);
{
    struct iter *i = 0;
    struct node *f = 0;
    i = malloc(sizeof(struct iter));
    if (i == 0) {
      abort();
    }
    
    f = l->first;
    //@ open llist_pred(l);
    //@ open node_pred(f);
    i->current = f;
    //@ close node_pred(f);
    //@ close llist_pred(l);
    //@ close iter_pred(i);
    return i;
}

int iter_next(struct iter *i)
  //@ requires iter_pred(i);
  //@ ensures iter_pred(i);
{
    struct node *c = i->current;
    //@ open iter_pred(i);
    //@ if(c != 0) open node_pred(c);
    int value = c->value;
    struct node *n = c->next;
    i->current = n;
    //@ if(c != 0) close node_pred(c);
    //@ close iter_pred(i);
    return value;
}

void iter_dispose(struct iter *i)
  //@ requires iter_pred(i);
  //@ ensures true;
{
    //@ open iter_pred(i);
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