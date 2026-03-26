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

predicate node(struct node *n; struct node *next, int value) =
  n->next |-> next &*& n->value |-> value;

predicate lseg(struct node *from, struct node *to; int count) =
  from == to ?
    count == 0
  :
    node(from, ?nxt, ?v) &*& lseg(nxt, to, ?c0) &*& count == c0 + 1;

predicate llist(struct llist *l; struct node *first, struct node *last, int count) =
  l->first |-> first &*& l->last |-> last &*& malloc_block_llist(l) &*&
  lseg(first, last, count) &*& node(last, 0, ?dummy);

predicate iter(struct iter *it; struct node *current) =
  it->current |-> current &*& malloc_block_iter(it);

@*/

struct llist *create_llist()
  //@ requires true;
  //@ ensures llist(result, ?f, ?la, 0);
{
  struct llist *l = malloc(sizeof(struct llist));
  if (l == 0) abort();
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) abort();
  //@ assume(n->next == 0);
  //@ assume(n->value == 0);
  l->first = n;
  l->last = n;
  //@ close node(n, 0, 0);
  //@ close lseg(n, n, 0);
  //@ close llist(l, n, n, 0);
  return l;
}

void llist_add(struct llist *list, int x)
  //@ requires llist(list, ?f, ?la, ?count);
  //@ ensures llist(list, f, ?la2, count + 1);
{
  //@ open llist(list, f, la, count);
  struct node *l = 0;
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) {
    abort();
  }
  //@ assume(n->next == 0);
  //@ assume(n->value == 0);
  l = list->last;
  //@ open node(l, 0, ?oldv);
  l->next = n;
  l->value = x;
  list->last = n;
  //@ close node(l, n, x);
  //@ close node(n, 0, 0);
  //@ close lseg(f, n, count + 1);
  //@ close llist(list, f, n, count + 1);
}

void llist_append(struct llist *list1, struct llist *list2)
  //@ requires llist(list1, ?f1, ?la1, ?c1) &*& llist(list2, ?f2, ?la2, ?c2);
  //@ ensures llist(list1, f1, ?la, c1 + c2);
{
  //@ open llist(list1, f1, la1, c1);
  //@ open llist(list2, f2, la2, c2);
  struct node *l1 = list1->last;
  struct node *f2 = list2->first;
  struct node *l2 = list2->last;

  if (f2 == l2) {
    //@ open node(l2, 0, ?dv2);
    free(l2);
    free(list2);
    //@ close llist(list1, f1, la1, c1);
  } else {
    //@ open lseg(f2, l2, c2);
    //@ open node(f2, ?f2n, ?f2v);
    //@ open node(l1, 0, ?dv1);
    l1->next = f2->next;
    l1->value = f2->value;
    list1->last = l2;

    free(f2);
    free(list2);

    //@ close node(l1, f2n, f2v);
    //@ close lseg(f1, l2, c1 + c2);
    //@ close llist(list1, f1, l2, c1 + c2);
  }
}

void llist_dispose(struct llist *list)
  //@ requires llist(list, ?f, ?la, ?count);
  //@ ensures true;
{
  //@ open llist(list, f, la, count);
  struct node *n = list->first;
  struct node *l = list->last;
  while (n != l)
    //@ invariant lseg(n, l, ?k) &*& node(l, 0, ?dv) &*& malloc_block_llist(list);
  {
    //@ open lseg(n, l, k);
    struct node *next = n->next;
    //@ open node(n, next, ?v);
    free(n);
    n = next;
    //@ close lseg(n, l, k - 1);
  }
  //@ open lseg(l, l, 0);
  //@ open node(l, 0, ?dv2);
  free(l);
  free(list);
}

int llist_length(struct llist *list)
  //@ requires llist(list, ?f, ?la, ?count);
  //@ ensures llist(list, f, la, count) &*& result == count;
{
  //@ open llist(list, f, la, count);
  struct node *f_ = list->first;
  struct node *n = f_;
  struct node *l = list->last;
  int c = 0;

  while (n != l)
    //@ invariant lseg(f_, n, c) &*& lseg(n, l, count - c) &*& node(l, 0, ?dv) &*& malloc_block_llist(list) &*& 0 <= c &*& c <= count;
  {
    //@ open lseg(n, l, count - c);
    struct node *next = n->next;
    //@ open node(n, next, ?v);
    //@ close node(n, next, v);
    n = next;
    if (c == INT_MAX) abort();
    c = c + 1;
    //@ close lseg(f_, n, c);
  }

  //@ open lseg(n, l, count - c);
  //@ close lseg(n, l, 0);
  //@ assert c == count;
  //@ close llist(list, f_, l, count);
  return c;
}

int llist_lookup(struct llist *list, int index)
  //@ requires llist(list, ?f, ?la, ?count) &*& 0 <= index &*& index < count;
  //@ ensures llist(list, f, la, count);
{
  //@ open llist(list, f, la, count);
  struct node *f_ = list->first;
  struct node *l = list->last;
  struct node *n = f_;
  int i = 0;
  while (i < index)
    //@ invariant lseg(f_, n, i) &*& lseg(n, l, count - i) &*& node(l, 0, ?dv) &*& malloc_block_llist(list) &*& 0 <= i &*& i <= index &*& index < count;
  {
    //@ open lseg(n, l, count - i);
    struct node *next = n->next;
    //@ open node(n, next, ?v);
    //@ close node(n, next, v);
    n = next;
    i = i + 1;
    //@ close lseg(f_, n, i);
  }

  //@ open lseg(n, l, count - index);
  //@ open node(n, ?nx, ?vv);
  int value = n->value;
  //@ close node(n, nx, vv);
  //@ close lseg(n, l, count - index);
  //@ close llist(list, f_, l, count);
  return value;
}

int llist_removeFirst(struct llist *l)
  //@ requires llist(l, ?f, ?la, ?count) &*& 0 < count;
  //@ ensures llist(l, ?f2, la, count - 1);
{
  //@ open llist(l, f, la, count);
  //@ open lseg(f, la, count);
  struct node *nf = l->first;

  struct node *nfn = nf->next;
  int nfv = nf->value;
  //@ open node(nf, nfn, nfv);
  free(nf);
  l->first = nfn;
  //@ close lseg(nfn, la, count - 1);
  //@ close llist(l, nfn, la, count - 1);
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
  //@ requires llist(l, ?f, ?la, ?count);
  //@ ensures llist(l, f, la, count) &*& iter(result, f);
{
    //@ open llist(l, f, la, count);
    struct iter *i = 0;
    struct node *f0 = 0;
    i = malloc(sizeof(struct iter));
    if (i == 0) {
      abort();
    }

    f0 = l->first;
    i->current = f0;

    //@ close llist(l, f, la, count);
    //@ close iter(i, f0);
    return i;
}

int iter_next(struct iter *i)
  //@ requires iter(i, ?c) &*& node(c, ?nxt, ?v);
  //@ ensures iter(i, nxt) &*& node(c, nxt, v) &*& result == v;
{
    //@ open iter(i, c);
    struct node *c0 = i->current;

    int value = c0->value;
    struct node *n = c0->next;

    i->current = n;

    //@ close iter(i, n);
    return value;
}

void iter_dispose(struct iter *i)
  //@ requires iter(i, ?c);
  //@ ensures true;
{
    //@ open iter(i, c);
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