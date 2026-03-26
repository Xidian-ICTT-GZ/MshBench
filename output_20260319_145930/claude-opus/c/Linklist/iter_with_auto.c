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
  n->next |-> next &*& n->value |-> value &*& malloc_block_node(n);

predicate lseg(struct node *first, struct node *last; list<int> vs) =
  first == last ?
    vs == nil
  :
    node(first, ?next, ?v) &*& lseg(next, last, ?vs0) &*& vs == cons(v, vs0);

predicate llist(struct llist *l; list<int> vs) =
  l->first |-> ?first &*& l->last |-> ?last &*& malloc_block_llist(l) &*&
  lseg(first, last, vs) &*& node(last, _, _);
@*/

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
  //@ close lseg(n, n, nil);
  //@ close llist(l, nil);
  return l;
}

/*@
lemma void lseg_add(struct node *first)
  requires lseg(first, ?last, ?vs) &*& node(last, ?next, ?v);
  ensures lseg(first, next, append(vs, cons(v, nil)));
{
  open lseg(first, last, vs);
  if (first == last) {
    close lseg(next, next, nil);
    close lseg(first, next, cons(v, nil));
  } else {
    lseg_add(?next0);
    close lseg(first, next, _);
  }
}
@*/

void llist_add(struct llist *list, int x)
  //@ requires llist(list, ?vs);
  //@ ensures llist(list, append(vs, cons(x, nil)));
{
  struct node *l = 0;
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) {
    abort();
  }
  //@ open llist(list, vs);
  l = list->last;
  //@ open node(l, _, _);
  l->next = n;
  l->value = x;
  list->last = n;
  //@ close node(l, n, x);
  //@ lseg_add(list->first);
  //@ close llist(list, append(vs, cons(x, nil)));
}

/*@
lemma void lseg_append(struct node *first, struct node *mid)
  requires lseg(first, mid, ?vs1) &*& lseg(mid, ?last, ?vs2);
  ensures lseg(first, last, append(vs1, vs2));
{
  open lseg(first, mid, vs1);
  if (first == mid) {
  } else {
    lseg_append(?next, mid);
    close lseg(first, last, _);
  }
}
@*/

void llist_append(struct llist *list1, struct llist *list2)
  //@ requires llist(list1, ?vs1) &*& llist(list2, ?vs2);
  //@ ensures llist(list1, append(vs1, vs2));
{
  //@ open llist(list1, vs1);
  //@ open llist(list2, vs2);
  struct node *l1 = list1->last;
  struct node *f2 = list2->first;
  struct node *l2 = list2->last;
  //@ open node(l1, _, _);
  if (f2 == l2) {
    //@ open lseg(f2, l2, vs2);
    //@ open node(l2, _, _);
    free(l2);
    free(list2);
    //@ close node(l1, _, _);
    //@ close llist(list1, vs1);
  } else {
    //@ open lseg(f2, l2, vs2);
    //@ open node(f2, ?f2next, ?f2v);
    l1->next = f2->next;
    l1->value = f2->value;
    list1->last = l2;
    //@ close node(l1, f2next, f2v);
    //@ lseg_add(list1->first);
    //@ lseg_append(list1->first, f2next);
    free(f2);
    free(list2);
    //@ close llist(list1, _);
  }
}

void llist_dispose(struct llist *list)
  //@ requires llist(list, ?vs);
  //@ ensures true;
{
  //@ open llist(list, vs);
  struct node *n = list->first;
  struct node *l = list->last;
  while (n != l)
    //@ invariant lseg(n, l, ?vs0) &*& node(l, _, _);
  {
    //@ open lseg(n, l, vs0);
    //@ open node(n, ?next, _);
    struct node *next = n->next;
    free(n);
    n = next;
  }
  //@ open lseg(n, l, _);
  //@ open node(l, _, _);
  free(l);
  free(list);
}

/*@
lemma void lseg_length_nonneg(struct node *first, struct node *last)
  requires lseg(first, last, ?vs);
  ensures lseg(first, last, vs) &*& 0 <= length(vs);
{
  open lseg(first, last, vs);
  if (first == last) {
    close lseg(first, last, vs);
  } else {
    lseg_length_nonneg(?next, last);
    close lseg(first, last, vs);
  }
}

lemma void lseg_to_lseg2(struct node *first, struct node *last)
  requires lseg(first, last, ?vs) &*& first != last;
  ensures lseg2(first, last, vs);
{
  open lseg(first, last, vs);
  if (first == last) {
  } else {
    open node(first, ?next, ?v);
    if (next == last) {
      close lseg2(next, last, nil);
    } else {
      close lseg(next, last, tail(vs));
      lseg_to_lseg2(next, last);
    }
    close lseg2(first, last, vs);
  }
}

predicate lseg2(struct node *first, struct node *last; list<int> vs) =
  first == last ?
    vs == nil
  :
    first->next |-> ?next &*& first->value |-> ?v &*& malloc_block_node(first) &*&
    lseg2(next, last, ?vs0) &*& vs == cons(v, vs0);

lemma void lseg2_to_lseg(struct node *first, struct node *last)
  requires lseg2(first, last, ?vs);
  ensures lseg(first, last, vs);
{
  open lseg2(first, last, vs);
  if (first == last) {
    close lseg(first, last, vs);
  } else {
    lseg2_to_lseg(?next, last);
    close node(first, ?n, ?v);
    close lseg(first, last, vs);
  }
}

lemma void lseg2_add_last(struct node *first)
  requires lseg2(first, ?last, ?vs) &*& last->next |-> ?next &*& last->value |-> ?v &*& malloc_block_node(last);
  ensures lseg2(first, next, append(vs, cons(v, nil))) &*& next->next |-> _;
{
  open lseg2(first, last, vs);
  if (first == last) {
    close lseg2(next, next, nil);
    close lseg2(first, next, cons(v, nil));
  } else {
    lseg2_add_last(?n);
    close lseg2(first, next, _);
  }
}
@*/

int llist_length(struct llist *list)
  //@ requires llist(list, ?vs) &*& length(vs) <= INT_MAX;
  //@ ensures llist(list, vs) &*& result == length(vs);
{
  //@ open llist(list, vs);
  struct node *f = list->first;
  struct node *n = f;
  struct node *l = list->last;
  int c = 0;
  //@ lseg_to_lseg2(f, l);
  while (n != l)
    //@ invariant lseg(f, n, ?vs1) &*& lseg2(n, l, ?vs2) &*& vs == append(vs1, vs2) &*& c == length(vs1) &*& length(vs1) + length(vs2) <= INT_MAX &*& node(l, _, _);
  {
    //@ open lseg2(n, l, vs2);
    struct node *next = n->next;
    //@ close node(n, next, ?v);
    //@ lseg_add(f);
    n = next;
    if (c == INT_MAX) abort();
    c = c + 1;
    //@ append_assoc(vs1, cons(v, nil), tail(vs2));
  }
  //@ open lseg2(n, l, _);
  //@ lseg2_to_lseg(n, l);
  //@ close llist(list, vs);
  //@ append_nil(vs1);
  return c;
}

/*@
lemma void lseg_split(struct node *first, struct node *last, int i)
  requires lseg(first, last, ?vs) &*& 0 <= i &*& i < length(vs);
  ensures lseg(first, ?mid, take(i, vs)) &*& node(mid, ?next, nth(i, vs)) &*& lseg(next, last, drop(i + 1, vs));
{
  open lseg(first, last, vs);
  if (i == 0) {
    close lseg(first, first, nil);
  } else {
    lseg_split(?next, last, i - 1);
    close lseg(first, ?mid, _);
  }
}

lemma void lseg_unsplit(struct node *first, struct node *mid, struct node *last)
  requires lseg(first, mid, ?vs1) &*& node(mid, ?next, ?v) &*& lseg(next, last, ?vs2);
  ensures lseg(first, last, append(vs1, cons(v, vs2)));
{
  open lseg(first, mid, vs1);
  if (first == mid) {
    close lseg(first, last, cons(v, vs2));
  } else {
    lseg_unsplit(?n, mid, last);
    close lseg(first, last, _);
  }
}
@*/

int llist_lookup(struct llist *list, int index)
  //@ requires llist(list, ?vs) &*& 0 <= index &*& index < length(vs);
  //@ ensures llist(list, vs) &*& result == nth(index, vs);
{
  //@ open llist(list, vs);
  struct node *f = list->first;
  struct node *l = list->last;
  struct node *n = f;
  int i = 0;
  //@ lseg_split(f, l, index);
  //@ close lseg(f, f, nil);
  while (i < index)
    //@ invariant lseg(f, n, ?vs1) &*& lseg(n, ?mid, ?vs2) &*& node(mid, ?mnext, nth(index, vs)) &*& lseg(mnext, l, ?vs3) &*& i == length(vs1) &*& i + length(vs2) == index &*& node(l, _, _);
  {
    //@ open lseg(n, mid, vs2);
    struct node *next = n->next;
    //@ lseg_add(f);
    n = next;
    i = i + 1;
  }
  //@ open lseg(n, ?mid, _);
  //@ open node(n, ?nnext, ?nv);
  int value = n->value;
  //@ close node(n, nnext, nv);
  //@ lseg_unsplit(f, n, l);
  //@ close llist(list, vs);
  return value;
}

int llist_removeFirst(struct llist *l)
  //@ requires llist(l, ?vs) &*& vs != nil;
  //@ ensures llist(l, tail(vs)) &*& result == head(vs);
{
  //@ open llist(l, vs);
  struct node *nf = l->first;
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

/*@
predicate llist_with_node(struct llist *l, struct node *n; list<int> vs1, list<int> vs2) =
  l->first |-> ?first &*& l->last |-> ?last &*& malloc_block_llist(l) &*&
  lseg(first, n, vs1) &*& lseg(n, last, vs2) &*& node(last, _, _);

predicate iter(struct iter *i, struct llist *l; list<int> vs1, list<int> vs2) =
  i->current |-> ?n &*& malloc_block_iter(i) &*& llist_with_node(l, n, vs1, vs2);
@*/

struct iter *llist_create_iter(struct llist *l)
    //@ requires llist(l, ?vs);
    //@ ensures iter(result, l, nil, vs);
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
    //@ close lseg(f, f, nil);
    //@ close llist_with_node(l, f, nil, vs);
    //@ close iter(i, l, nil, vs);
    return i;
}

int iter_next(struct iter *i)
    //@ requires iter(i, ?l, ?vs1, ?vs2) &*& vs2 != nil;
    //@ ensures iter(i, l, append(vs1, cons(head(vs2), nil)), tail(vs2)) &*& result == head(vs2);
{
    //@ open iter(i, l, vs1, vs2);
    struct node *c = i->current;
    //@ open llist_with_node(l, c, vs1, vs2);
    //@ open lseg(c, ?last, vs2);
    //@ open node(c, ?next, ?v);
    int value = c->value;
    struct node *n = c->next;
    //@ close node(c, next, v);
    //@ lseg_add(l->first);
    i->current = n;
    //@ close llist_with_node(l, n, append(vs1, cons(v, nil)), tail(vs2));
    //@ close iter(i, l, append(vs1, cons(v, nil)), tail(vs2));
    return value;
}

void iter_dispose(struct iter *i)
    //@ requires iter(i, ?l, ?vs1, ?vs2);
    //@ ensures llist(l, append(vs1, vs2));
{
    //@ open iter(i, l, vs1, vs2);
    //@ open llist_with_node(l, ?n, vs1, vs2);
    //@ lseg_append(l->first, n);
    //@ close llist(l, append(vs1, vs2));
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
    //@ open iter(i1, l, nil, ?vs);
    //@ open llist_with_node(l, ?n1, nil, vs);
    //@ close llist_with_node(l, n1, nil, vs);
    //@ close iter(i1, l, nil, vs);
    //@ open iter(i1, l, nil, vs);
    //@ open llist_with_node(l, n1, nil, vs);
    //@ lseg_append(l->first, n1);
    //@ close llist(l, vs);
    struct iter *i2 = llist_create_iter(l);
    //@ open iter(i2, l, nil, vs);
    //@ open llist_with_node(l, ?n2, nil, vs);
    //@ open lseg(n2, ?last, vs);
    //@ close lseg(n2, last, vs);
    //@ lseg_to_lseg2(n2, last);
    //@ open lseg2(n2, last, vs);
    //@ close lseg(n2, n2, nil);
    //@ close lseg2(n2, last, vs);
    //@ lseg2_to_lseg(n2, last);
    //@ close llist_with_node(l, n2, nil, vs);
    //@ close iter(i2, l, nil, vs);
    //@ open iter(i2, l, nil, vs);
    //@ open llist_with_node(l, n2, nil, vs);
    //@ close lseg(n1, n1, nil);
    //@ close llist_with_node(l, n1, nil, vs);
    //@ close iter(i1, l, nil, vs);
    int i1e1 = iter_next(i1); assert(i1e1 == 5);
    //@ open iter(i1, l, ?vs1a, ?vs2a);
    //@ open llist_with_node(l, ?n1a, vs1a, vs2a);
    //@ close lseg(n2, n2, nil);
    //@ close llist_with_node(l, n2, nil, append(vs1a, vs2a));
    //@ close iter(i2, l, nil, append(vs1a, vs2a));
    int i2e1 = iter_next(i2); assert(i2e1 == 5);
    //@ open iter(i2, l, ?vs1b, ?vs2b);
    //@ open llist_with_node(l, ?n2b, vs1b, vs2b);
    //@ close llist_with_node(l, n1a, vs1a, vs2a);
    //@ close iter(i1, l, vs1a, vs2a);
    int i1e2 = iter_next(i1); assert(i1e2 == 10);
    //@ open iter(i1, l, ?vs1c, ?vs2c);
    //@ open llist_with_node(l, ?n1c, vs1c, vs2c);
    //@ close llist_with_node(l, n2b, vs1b, vs2b);
    //@ close iter(i2, l, vs1b, vs2b);
    int i2e2 = iter_next(i2); assert(i2e2 == 10);
    //@ open iter(i2, l, ?vs1d, ?vs2d);
    //@ open llist_with_node(l, ?n2d, vs1d, vs2d);
    //@ open malloc_block_iter(i1);
    //@ close malloc_block_iter(i1);
    //@ close llist_with_node(l, n1c, vs1c, vs2c);
    //@ close iter(i1, l, vs1c, vs2c);
    iter_dispose(i1);
    //@ open llist(l, ?vsfinal);
    //@ close llist_with_node(l, n2d, vs1d, vs2d);
    //@ close iter(i2, l, vs1d, vs2d);
    iter_dispose(i2);
    llist_dispose(l);
    return 0;
}