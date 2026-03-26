#include "stdlib.h"

struct node {
  struct node *next;
  int value;
};

struct llist {
  struct node *first;
  struct node *last;
};

/*@
predicate nodes(struct node *first, struct node *last, int count) =
  first == last ?
    count == 0
  :
    first->next |-> ?next &*& first->value |-> ?v &*& malloc_block_node(first) &*&
    nodes(next, last, ?ncount) &*& count == ncount + 1;

predicate llist(struct llist *l, int count) =
  l->first |-> ?first &*& l->last |-> ?last &*& malloc_block_llist(l) &*&
  nodes(first, last, count);
@*/

struct llist *create_llist()
  //@ requires true;
  //@ ensures llist(result, 0);
{
  struct llist *l = malloc(sizeof(struct llist));
  if (l == 0) abort();
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) abort();
  l->first = n;
  l->last = n;
  //@ close nodes(n, n, 0);
  //@ close llist(l, 0);
  return l;
}

void llist_add(struct llist *list, int x)
  //@ requires llist(list, ?count);
  //@ ensures llist(list, count + 1);
{
  struct node *l = 0;
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) {
    abort();
  }
  l = list->last;
  l->next = n;
  l->value = x;
  list->last = n;
  //@ open nodes(list->first, l, count);
  //@ close nodes(list->first, n, count + 1);
  //@ close llist(list, count + 1);
}

void llist_append(struct llist *list1, struct llist *list2)
  //@ requires llist(list1, ?c1) &*& llist(list2, ?c2);
  //@ ensures llist(list1, c1 + c2);
{
  struct node *l1 = list1->last;
  struct node *f2 = list2->first;
  struct node *l2 = list2->last;
  
  if (f2 == l2) {
    //@ open nodes(f2, l2, c2);
    free(l2);
    free(list2);
    //@ close llist(list1, c1 + c2);
  } else {
    //@ open nodes(f2, l2, c2);
    l1->next = f2->next;
    l1->value = f2->value;
    list1->last = l2;
    free(f2);
    free(list2);
    //@ close llist(list1, c1 + c2);
  }
}

void llist_dispose(struct llist *list)
  //@ requires llist(list, _);
  //@ ensures true;
{
  struct node *n = list->first;
  struct node *l = list->last;
  //@ open llist(list, _);
  //@ open nodes(n, l, _);
  while (n != l)
    //@ invariant nodes(n, l, _);
  {
    struct node *next = n->next;
    free(n);
    n = next;
    //@ open nodes(n, l, _);
  }
  free(l);
  free(list);
}

int llist_length(struct llist *list)
  //@ requires llist(list, ?count);
  //@ ensures llist(list, count) &*& result == count;
{
  struct node *f = list->first;
  struct node *n = f;
  struct node *l = list->last;
  int c = 0;
  //@ open llist(list, count);
  //@ open nodes(f, l, count);
  while (n != l)
    //@ invariant nodes(n, l, ?rem) &*& c + rem == count;
  {
    struct node *next = n->next;
    n = next;
    if (c == INT_MAX) abort();
    c = c + 1;
    //@ open nodes(n, l, _);
  }
  //@ close nodes(f, l, count);
  //@ close llist(list, count);
  return c;
}

int llist_lookup(struct llist *list, int index)
  //@ requires llist(list, ?count) &*& 0 <= index &*& index < count;
  //@ ensures llist(list, count);
{
  struct node *f = list->first;
  struct node *l = list->last;
  struct node *n = f;
  int i = 0;
  //@ open llist(list, count);
  //@ open nodes(f, l, count);
  while (i < index)
    //@ invariant nodes(n, l, ?rem) &*& i + rem == count &*& 0 <= i;
  {
    struct node *next = n->next;
    n = next;
    i = i + 1;
    //@ open nodes(n, l, _);
  }
  int value = n->value;
  //@ close nodes(f, l, count);
  //@ close llist(list, count);
  return value;
}

int llist_removeFirst(struct llist *l)
  //@ requires llist(l, ?count) &*& count > 0;
  //@ ensures llist(l, count - 1);
{
  struct node *nf = l->first;
  struct node *nfn = nf->next;
  int nfv = nf->value;
  free(nf);
  l->first = nfn;
  //@ open llist(l, count);
  //@ open nodes(nf, l->last, count);
  //@ close llist(l, count - 1);
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
predicate iter(struct iter *i, struct node *current) =
  i->current |-> current &*& malloc_block_iter(i);
@*/

struct iter *llist_create_iter(struct llist *l)
    //@ requires llist(l, ?count);
    //@ ensures llist(l, count) &*& iter(result, l->first);
{
    struct iter *i = 0;
    struct node *f = 0;
    i = malloc(sizeof(struct iter));
    if (i == 0) {
      abort();
    }
    //@ open llist(l, count);
    f = l->first;
    i->current = f;
    //@ close llist(l, count);
    //@ close iter(i, f);
    return i;
}

int iter_next(struct iter *i)
    //@ requires iter(i, ?current);
    //@ ensures iter(i, ?next) &*& result == current->value;
{
    struct node *c = i->current;
    int value = c->value;
    struct node *n = c->next;
    i->current = n;
    //@ open iter(i, current);
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
    int i1e1 = iter_next(i1); assert(i1e1 == 5);
    int i2e1 = iter_next(i2); assert(i2e1 == 5);
    int i1e2 = iter_next(i1); assert(i1e2 == 10);
    int i2e2 = iter_next(i2); assert(i2e2 == 10);
    iter_dispose(i1);
    iter_dispose(i2);
    llist_dispose(l);
    return 0;
}