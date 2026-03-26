#include "stdlib.h"

/*@
predicate node(struct node *node; struct node *next, int value) =
    node->next |-> next &*& node->value |-> value &*& malloc_block_node(node);
@*/

/*@
predicate lseg(struct node *first, struct node *last; list<int> values) =
    first == last ?
        values == nil
    :
        node(first, ?next, ?value) &*& lseg(next, last, ?vs) &*& values == cons(value, vs);
@*/

/*@
predicate llist(struct llist *list; list<int> values) =
    list->first |-> ?first &*& list->last |-> ?last &*& malloc_block_llist(list) &*& lseg(first, last, values) &*& node(last, _, _);
@*/

/*@
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

struct llist *create_llist()
  //@ requires true;
  //@ ensures llist(result, nil);
{
  struct llist *l = malloc(sizeof(struct llist));
  if (l == 0) abort();
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) abort();
  l->first = n;
  l->last = n;
  //@ close node(n, _, _);
  //@ close lseg(n, n, nil);
  //@ close llist(l, nil);
  return l;
}

void llist_add(struct llist *list, int x)
  //@ requires llist(list, ?vs);
  //@ ensures llist(list, append(vs, cons(x, nil)));
{
  struct node *l = 0;
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) {
    abort();
  }
  l = list->last;
  //@ open llist(list, vs);
  //@ open lseg(_, _, _);
  //@ open node(l, _, _);
  l->next = n;
  l->value = x;
  list->last = n;
  //@ close node(l, n, x);
  //@ close node(n, _, _);
  //@ close lseg(n, n, nil);
  //@ close lseg(l, n, cons(x, nil));
  //@ close llist(list, append(vs, cons(x, nil)));
}

void llist_append(struct llist *list1, struct llist *list2)
  //@ requires llist(list1, ?vs1) &*& llist(list2, ?vs2);
  //@ ensures llist(list1, append(vs1, tail(vs2)));
{
  struct node *l1 = list1->last;
  struct node *f2 = list2->first;
  struct node *l2 = list2->last;
  //@ open llist(list1, vs1);
  //@ open llist(list2, vs2);
  //@ open lseg(_, _, _);
  //@ open node(l1, _, _);
  //@ open lseg(f2, l2, vs2);
  if (f2 == l2) {
    //@ open node(l2, _, _);
    free(l2);
    free(list2);
    //@ close node(l1, _, _);
    //@ close lseg(l1, l1, nil);
    //@ close llist(list1, vs1);
  } else {
    //@ open node(f2, ?next2, ?v2);
    l1->next = f2->next;
    l1->value = f2->value;
    list1->last = l2;
    free(f2);
    free(list2);
    //@ close node(l1, next2, v2);
    //@ close lseg(next2, l2, tail(vs2));
    //@ close llist(list1, append(vs1, tail(vs2)));
  }
}

void llist_dispose(struct llist *list)
  //@ requires llist(list, _);
  //@ ensures true;
{
  struct node *n = list->first;
  struct node *l = list->last;
  //@ open llist(list, _);
  //@ open lseg(_, _, _);
  while (n != l)
    //@ invariant lseg(n, l, _);
  {
    //@ open lseg(n, l, _);
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
  //@ requires llist(list, ?vs);
  //@ ensures llist(list, vs) &*& result == length(vs);
{
  struct node *f = list->first;
  struct node *n = f;
  struct node *l = list->last;
  int c = 0;
  //@ open llist(list, vs);
  //@ open lseg(f, l, vs);
  while (n != l)
    //@ invariant lseg(n, l, ?vs1) &*& c + length(vs1) == length(vs);
  {
    //@ open lseg(n, l, vs1);
    struct node *next = n->next;
    //@ open node(n, _, _);
    n = next;
    if (c == INT_MAX) abort();
    c = c + 1;
  }
  //@ close lseg(l, l, nil);
  //@ close llist(list, vs);
  return c;
}

int llist_lookup(struct llist *list, int index)
  //@ requires llist(list, ?vs) &*& 0 <= index &*& index < length(vs);
  //@ ensures llist(list, vs) &*& result == nth(index, vs);
{
  struct node *f = list->first;
  struct node *l = list->last;
  struct node *n = f;
  int i = 0;
  //@ open llist(list, vs);
  //@ open lseg(f, l, vs);
  while (i < index)
    //@ invariant lseg(n, l, ?vs1) &*& i + length(vs1) == length(vs) &*& nth(i, vs) == head(vs1);
  {
    //@ open lseg(n, l, vs1);
    struct node *next = n->next;
    //@ open node(n, _, _);
    n = next;
    i = i + 1;
  }
  //@ open lseg(n, l, ?vs2);
  //@ open node(n, _, _);
  int value = n->value;
  //@ close node(n, _, _);
  //@ close lseg(n, l, vs2);
  //@ close lseg(f, l, vs);
  //@ close llist(list, vs);
  return value;
}

int llist_removeFirst(struct llist *l)
  //@ requires llist(l, ?vs) &*& vs != nil;
  //@ ensures llist(l, tail(vs)) &*& result == head(vs);
{
  struct node *nf = l->first;
  //@ open llist(l, vs);
  //@ open lseg(nf, ?last, vs);
  //@ open node(nf, ?nfn, ?nfv);
  struct node *nfn = nf->next;
  int nfv = nf->value;
  free(nf);
  l->first = nfn;
  //@ close llist(l, tail(vs));
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

struct iter *llist_create_iter(struct llist *l)
    //@ requires llist(l, ?vs);
    //@ ensures iter(result, ?c) &*& lseg(c, ?last, ?vs1) &*& node(last, _, _) &*& c == l->first;
{
    struct iter *i = 0;
    struct node *f = 0;
    i = malloc(sizeof(struct iter));
    if (i == 0) {
      abort();
    }
    //@ open llist(l, vs);
    f = l->first;
    i->current = f;
    //@ close iter(i, f);
    //@ close lseg(f, l->last, vs);
    //@ close node(l->last, _, _);
    return i;
}

int iter_next(struct iter *i)
    //@ requires iter(i, ?c) &*& lseg(c, ?last, ?vs) &*& node(last, _, _) &*& vs != nil;
    //@ ensures iter(i, ?next) &*& lseg(next, last, tail(vs)) &*& node(last, _, _) &*& result == head(vs);
{
    //@ open lseg(c, last, vs);
    //@ open node(c, ?next, ?value);
    struct node *c = i->current;
    int value = c->value;
    struct node *n = c->next;
    i->current = n;
    //@ close iter(i, n);
    //@ close lseg(n, last, tail(vs));
    //@ close node(last, _, _);
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