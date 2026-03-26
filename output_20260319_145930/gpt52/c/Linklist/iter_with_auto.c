#include "stdlib.h"
#include "limits.h"

/*@

predicate nodes(struct node *from, struct node *to; int len) =
  from == to ?
    len == 0
  :
    from != 0 &*& from->next |-> ?n &*& from->value |-> _ &*& malloc_block_node(from) &*&
    nodes(n, to, ?len0) &*& len == len0 + 1;

predicate llist(struct llist *l; struct node *first, struct node *last, int len) =
  l->first |-> first &*& l->last |-> last &*& malloc_block_llist(l) &*&
  first != 0 &*& last != 0 &*& nodes(first, last, len) &*&
  last->next |-> _ &*& last->value |-> _ &*& malloc_block_node(last);

predicate iter(struct iter *it; struct node *cur) =
  it->current |-> cur &*& malloc_block_iter(it);

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
  //@ ensures llist(result, ?f, ?la, 0);
{
  struct llist *l = malloc(sizeof(struct llist));
  if (l == 0) abort();
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) abort();
  l->first = n;
  l->last = n;
  //@ close nodes(n, n, 0);
  //@ close llist(l, n, n, 0);
  return l;
}

void llist_add(struct llist *list, int x)
  //@ requires llist(list, ?f, ?la, ?len);
  //@ ensures llist(list, f, ?la2, len + 1);
{
  //@ open llist(list, f, la, len);
  struct node *l = 0;
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) {
    abort();
  }
  l = list->last;
  l->next = n;
  l->value = x;
  list->last = n;
  //@ close nodes(f, l, len + 1);
  //@ close llist(list, f, n, len + 1);
}

void llist_append(struct llist *list1, struct llist *list2)
  //@ requires llist(list1, ?f1, ?la1, ?len1) &*& llist(list2, ?f2, ?la2, ?len2);
  //@ ensures llist(list1, f1, ?la, len1 + len2);
{
  //@ open llist(list1, f1, la1, len1);
  //@ open llist(list2, f2, la2, len2);
  struct node *l1 = list1->last;
  struct node *f2 = list2->first;
  struct node *l2 = list2->last;

  if (f2 == l2) {
    //@ open nodes(f2, l2, len2);
    //@ assert len2 == 0;
    free(l2);
    free(list2);
    //@ close llist(list1, f1, la1, len1);
  } else {
    //@ open nodes(f2, l2, len2);
    //@ assert f2 != l2;
    struct node *f2next = f2->next;
    l1->next = f2->next;
    l1->value = f2->value;
    list1->last = l2;

    free(f2);
    free(list2);
    //@ close nodes(f2next, l2, len2 - 1);
    //@ close nodes(f1, l1, len1 + len2);
    //@ close llist(list1, f1, l2, len1 + len2);
  }
}

void llist_dispose(struct llist *list)
  //@ requires llist(list, ?f, ?la, ?len);
  //@ ensures true;
{
  //@ open llist(list, f, la, len);
  struct node *n = list->first;
  struct node *l = list->last;
  //@ close nodes(n, l, len);
  while (n != l)
    //@ invariant nodes(n, l, ?k);
  {
    //@ open nodes(n, l, k);
    struct node *next = n->next;
    free(n);
    n = next;
  }
  //@ open nodes(n, l, ?k0);
  //@ assert k0 == 0;
  free(l);
  free(list);
}

int llist_length(struct llist *list)
  //@ requires llist(list, ?f, ?la, ?len);
  //@ ensures llist(list, f, la, len) &*& result == len;
{
  //@ open llist(list, f, la, len);
  struct node *f_ = list->first;
  struct node *n = f_;
  struct node *l = list->last;
  int c = 0;

  //@ close nodes(n, l, len);
  while (n != l)
    //@ invariant nodes(n, l, ?k) &*& c + k == len &*& 0 <= c;
  {
    //@ open nodes(n, l, k);
    struct node *next = n->next;

    n = next;
    if (c == INT_MAX) abort();
    c = c + 1;
    //@ close nodes(n, l, k - 1);
  }

  //@ open nodes(n, l, ?k0);
  //@ assert k0 == 0;
  //@ close nodes(f_, l, len);
  //@ close llist(list, f, la, len);
  return c;
}

int llist_lookup(struct llist *list, int index)
  //@ requires llist(list, ?f, ?la, ?len) &*& 0 <= index &*& index < len;
  //@ ensures llist(list, f, la, len);
{
  //@ open llist(list, f, la, len);
  struct node *f_ = list->first;
  struct node *l = list->last;
  struct node *n = f_;
  int i = 0;
  //@ close nodes(n, l, len);
  while (i < index)
    //@ invariant nodes(n, l, ?k) &*& 0 <= i &*& i < len &*& k == len - i;
  {
    //@ open nodes(n, l, k);
    struct node *next = n->next;

    n = next;
    i = i + 1;
    //@ close nodes(n, l, k - 1);
  }

  //@ open nodes(n, l, ?kfin);
  int value = n->value;
  //@ close nodes(n, l, kfin);
  //@ close nodes(f_, l, len);
  //@ close llist(list, f, la, len);

  return value;
}

int llist_removeFirst(struct llist *l)
  //@ requires llist(l, ?f, ?la, ?len) &*& 0 < len;
  //@ ensures llist(l, ?f2, la, len - 1);
{
  //@ open llist(l, f, la, len);
  //@ open nodes(f, la, len);
  struct node *nf = l->first;

  struct node *nfn = nf->next;
  int nfv = nf->value;
  free(nf);
  l->first = nfn;
  //@ close llist(l, nfn, la, len - 1);
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
    //@ requires llist(l, ?f, ?la, ?len);
    //@ ensures llist(l, f, la, len) &*& iter(result, f);
{
    //@ open llist(l, f, la, len);
    struct iter *i = 0;
    struct node *f0 = 0;
    i = malloc(sizeof(struct iter));
    if (i == 0) {
      abort();
    }

    f0 = l->first;
    i->current = f0;

    //@ close llist(l, f, la, len);
    //@ close iter(i, f0);
    return i;
}

int iter_next(struct iter *i)
    //@ requires iter(i, ?cur) &*& cur != 0 &*& cur->next |-> ?n &*& cur->value |-> ?v;
    //@ ensures iter(i, n) &*& cur->next |-> n &*& cur->value |-> v &*& result == v;
{
    //@ open iter(i, cur);
    struct node *c = i->current;

    int value = c->value;
    struct node *n = c->next;

    i->current = n;

    //@ close iter(i, n);
    return value;
}

void iter_dispose(struct iter *i)
    //@ requires iter(i, ?cur);
    //@ ensures true;
{
    //@ open iter(i, cur);
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
    //@ open llist(l, ?f, ?la, ?len);
    //@ close llist(l, f, la, len);
    int i1e1 = iter_next(i1); assert(i1e1 == 5);
    int i2e1 = iter_next(i2); assert(i2e1 == 5);
    int i1e2 = iter_next(i1); assert(i1e2 == 10);
    int i2e2 = iter_next(i2); assert(i2e2 == 10);
    iter_dispose(i1);
    iter_dispose(i2);
    llist_dispose(l);
    return 0;
}