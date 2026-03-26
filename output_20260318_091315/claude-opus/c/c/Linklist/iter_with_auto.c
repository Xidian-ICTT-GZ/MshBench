#include "stdlib.h"

/*@ 
predicate node(struct node *n; int *contents, int length) =
  n == 0 ?
    contents == null &*& length == 0
  :
    n->value |-> ?v &*& n->next |-> ?nx &*& malloc_block_node(n) &*&
    node(nx, ?tailContents, ?tailLength) &*&
    contents == cons(v, tailContents) &*& length == 1 + tailLength;

predicate nodes(struct node *first, struct node *last; list<int> vs) =
  first == last ?
    vs == nil &*& first != 0 &*& malloc_block_node(first)
  :
    first != 0 &*& first->value |-> ?v &*& first->next |-> ?nx &*&
    malloc_block_node(first) &*& nodes(nx, last, ?tail) &*& vs == cons(v, tail);

predicate llist(struct llist *list; list<int> vs) =
  list != 0 &*&
  list->first |-> ?first &*& list->last |-> ?last &*& malloc_block_llist(list) &*&
  nodes(first, last, vs);

predicate iter(struct iter *it; struct node *cur; list<int> vs) =
  it != 0 &*&
  it->current |-> cur &*& malloc_block_iter(it) &*&
  node(cur, ?contents, ?len) &*& vs == (contents == null ? nil : contents);

/*@ lemma void nodes_append(struct node *f1, struct node *l1, struct node *f2, struct node *l2, list<int> v1, list<int> v2)
  requires nodes(f1, l1, v1) &*& nodes(f2, l2, v2) &*& l1 != 0 &*& l2 != 0;
  ensures nodes(f1, l2, append(v1, v2));
{
  open nodes(f1, l1, v1);
  open nodes(f2, l2, v2);
  if (f1 == l1) {
    close nodes(f1, l2, append(v1, v2));
  } else {
    nodes_append(f1->next, l1, f2, l2, tail(v1), v2);
    close nodes(f1, l2, append(v1, v2));
  }
}
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
  //@ close nodes(n, n, nil);
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
  l->next = n;
  l->value = x;
  list->last = n;
  //@ open nodes(list->first, list->last, vs);
  //@ open nodes(l, list->last, ?tail);
  //@ close nodes(n, n, nil);
  //@ nodes_append(list->first, l, n, n, vs, cons(x, nil));
  //@ close llist(list, append(vs, cons(x, nil)));
}

void llist_append(struct llist *list1, struct llist *list2)
  //@ requires llist(list1, ?vs1) &*& llist(list2, ?vs2);
  //@ ensures llist(list1, append(vs1, vs2)) &*& true;
{
  struct node *l1 = list1->last;
  struct node *f2 = list2->first;
  struct node *l2 = list2->last;

  if (f2 == l2) {
    free(l2);
    free(list2);
    //@ open nodes(list1->first, l1, vs1);
    //@ open nodes(list2->first, l2, vs2);
    //@ close llist(list1, vs1);
  } else {
    l1->next = f2->next;
    l1->value = f2->value;
    list1->last = l2;

    free(f2);
    free(list2);
    //@ open nodes(list1->first, l1, vs1);
    //@ open nodes(list2->first, l2, cons(?v, ?tail));
    //@ close nodes(list1->first, l2, append(vs1, cons(v, tail)));
    //@ close llist(list1, append(vs1, cons(v, tail)));
  }
}

void llist_dispose(struct llist *list)
  //@ requires llist(list, ?vs);
  //@ ensures true;
{
  struct node *n = list->first;
  struct node *l = list->last;
  //@ open llist(list, vs);
  //@ open nodes(n, l, vs);

  while (n != l)
  //@ invariant n != 0 &*& l != 0 &*& nodes(n, l, ?mid);
  {
    struct node *next = n->next;
    free(n);
    n = next;
  }

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
  //@ open nodes(f, l, vs);

  while (n != l)
  //@ invariant n != 0 &*& l != 0 &*& nodes(n, l, ?mid) &*& c == length(take(length(vs) - length(mid), vs));
  {
    struct node *next = n->next;
    n = next;
    if (c == INT_MAX) abort();
    c = c + 1;
  }

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
  //@ open nodes(f, l, vs);

  while (i < index)
  //@ invariant n != 0 &*& l != 0 &*& nodes(n, l, ?mid) &*& i <= index &*&
  //@           length(take(i, vs)) + length(mid) == length(vs);
  {
    struct node *next = n->next;
    n = next;
    i = i + 1;
  }

  int value = n->value;
  //@ close llist(list, vs);
  return value;
}

int llist_removeFirst(struct llist *l)
  //@ requires llist(l, ?vs) &*& vs != nil;
  //@ ensures llist(l, tail(vs)) &*& result == head(vs);
{
  struct node *nf = l->first;
  //@ open llist(l, vs);
  //@ open nodes(nf, l->last, vs);
  //@ open nodes(nf, l->last, cons(?v, ?tail));
  struct node *nfn = nf->next;
  int nfv = nf->value;
  free(nf);
  l->first = nfn;
  //@ close nodes(nfn, l->last, tail);
  //@ close llist(l, tail);
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
  //@ requires llist(l, ?vs) &*& vs != nil;
  //@ ensures iter(result, l->first->next, tail(vs)) &*& malloc_block_iter(result);
{
  struct iter *i = 0;
  struct node *f = 0;
  i = malloc(sizeof(struct iter));
  if (i == 0) {
    abort();
  }

  f = l->first;
  i->current = f;

  //@ close iter(i, f, vs);
  return i;
}

int iter_next(struct iter *i)
  //@ requires iter(i, ?cur, ?vs) &*& vs != nil;
  //@ ensures iter(i, cur->next, tail(vs)) &*& result == head(vs);
{
  struct node *c = i->current;

  int value = c->value;
  struct node *n = c->next;

  i->current = n;

  //@ open node(c, ?contents, ?len);
  //@ assert contents == cons(value, ?tail);
  //@ close iter(i, n, tail);
  return value;
}

void iter_dispose(struct iter *i)
  //@ requires iter(i, ?cur, ?vs);
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