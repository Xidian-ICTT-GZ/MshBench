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
predicate nodes(struct node *from, struct node *to, int count) =
  from == to ?
    count == 0
  :
    from != 0 &*& from->next |-> ?next &*& from->value |-> ?v &*& malloc_block_node(from) &*&
    nodes(next, to, ?c2) &*& count == c2 + 1;

predicate llist(struct llist *l, int count) =
  l->first |-> ?f &*& l->last |-> ?last &*& malloc_block_llist(l) &*&
  last != 0 &*& last->next |-> _ &*& last->value |-> _ &*& malloc_block_node(last) &*&
  nodes(f, last, count);

predicate lseg(struct node *from, struct node *to, int count) =
  from == to ?
    count == 0
  :
    from != 0 &*& from->next |-> ?next &*& from->value |-> ?v &*&
    lseg(next, to, ?c2) &*& count == c2 + 1;
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

/*@
lemma void nodes_add(struct node *from)
  requires nodes(from, ?to, ?count) &*& to->next |-> ?nn &*& to->value |-> ?v &*& malloc_block_node(to) &*& nn != 0;
  ensures nodes(from, nn, count + 1) &*& nn->next |-> _ &*& nn->value |-> _ &*& malloc_block_node(nn);
{
  open nodes(from, to, count);
  if (from == to) {
    close nodes(nn, nn, 0);
    close nodes(to, nn, 1);
  } else {
    nodes_add(from->next);
    close nodes(from, nn, count + 1);
  }
}
@*/

void llist_add(struct llist *list, int x)
  //@ requires llist(list, ?count);
  //@ ensures llist(list, count + 1);
{
  struct node *l = 0;
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) {
    abort();
  }
  //@ open llist(list, count);
  l = list->last;
  l->next = n;
  l->value = x;
  list->last = n;
  //@ nodes_add(list->first);
  //@ close llist(list, count + 1);
}

/*@
lemma void nodes_append(struct node *from1, struct node *to1, struct node *from2, struct node *to2)
  requires nodes(from1, to1, ?c1) &*& to1->next |-> from2 &*& to1->value |-> ?v &*& malloc_block_node(to1) &*& nodes(from2, to2, ?c2);
  ensures nodes(from1, to2, c1 + c2 + 1);
{
  open nodes(from1, to1, c1);
  if (from1 == to1) {
    close nodes(from2, to2, c2);
    close nodes(to1, to2, c2 + 1);
  } else {
    nodes_append(from1->next, to1, from2, to2);
    close nodes(from1, to2, c1 + c2 + 1);
  }
}
@*/

void llist_append(struct llist *list1, struct llist *list2)
  //@ requires llist(list1, ?c1) &*& llist(list2, ?c2);
  //@ ensures llist(list1, c1 + c2);
{
  //@ open llist(list1, c1);
  //@ open llist(list2, c2);
  struct node *l1 = list1->last;
  struct node *f2 = list2->first;
  struct node *l2 = list2->last;
  //@ open nodes(f2, l2, c2);
  if (f2 == l2) {
    //@ close nodes(l1, l1, 0);
    //@ close llist(list1, c1);
    free(l2);
    free(list2);
    //@ open llist(list1, c1);
    //@ close llist(list1, c1 + 0);
  } else {
    l1->next = f2->next;
    l1->value = f2->value;
    list1->last = l2;
    //@ nodes_append(list1->first, l1, f2->next, l2);
    //@ close llist(list1, c1 + c2);
    free(f2);
    free(list2);
  }
}

void llist_dispose(struct llist *list)
  //@ requires llist(list, ?count);
  //@ ensures true;
{
  //@ open llist(list, count);
  struct node *n = list->first;
  struct node *l = list->last;
  while (n != l)
    //@ invariant nodes(n, l, ?c) &*& l->next |-> _ &*& l->value |-> _ &*& malloc_block_node(l);
  {
    //@ open nodes(n, l, c);
    struct node *next = n->next;
    free(n);
    n = next;
  }
  //@ open nodes(l, l, _);
  free(l);
  free(list);
}

/*@
lemma void nodes_to_lseg(struct node *from)
  requires nodes(from, ?to, ?count);
  ensures lseg(from, to, count) &*& (from == to ? true : malloc_block_node(from));
{
  open nodes(from, to, count);
  if (from == to) {
    close lseg(from, to, 0);
  } else {
    nodes_to_lseg(from->next);
    close lseg(from, to, count);
  }
}

lemma void lseg_to_nodes(struct node *from)
  requires lseg(from, ?to, ?count) &*& (from == to ? true : malloc_block_node(from));
  ensures nodes(from, to, count);
{
  open lseg(from, to, count);
  if (from == to) {
    close nodes(from, to, 0);
  } else {
    lseg_to_nodes(from->next);
    close nodes(from, to, count);
  }
}

lemma void lseg_add(struct node *from)
  requires lseg(from, ?to, ?count) &*& to->next |-> ?next &*& to->value |-> ?v &*& (from == to ? true : malloc_block_node(from)) &*& malloc_block_node(to);
  ensures lseg(from, next, count + 1) &*& (from == next ? true : malloc_block_node(from));
{
  open lseg(from, to, count);
  if (from == to) {
    close lseg(next, next, 0);
    close lseg(to, next, 1);
  } else {
    lseg_add(from->next);
    close lseg(from, next, count + 1);
  }
}

lemma void lseg_append_node(struct node *from)
  requires lseg(from, ?mid, ?c1) &*& mid->next |-> ?to &*& mid->value |-> ?v &*& (from == mid ? true : malloc_block_node(from)) &*& malloc_block_node(mid);
  ensures lseg(from, to, c1 + 1) &*& (from == to ? true : malloc_block_node(from));
{
  lseg_add(from);
}
@*/

int llist_length(struct llist *list)
  //@ requires llist(list, ?count) &*& count <= INT_MAX;
  //@ ensures llist(list, count) &*& result == count;
{
  //@ open llist(list, count);
  struct node *f = list->first;
  struct node *n = f;
  struct node *l = list->last;
  int c = 0;
  //@ nodes_to_lseg(f);
  while (n != l)
    //@ invariant lseg(f, n, ?c1) &*& lseg(n, l, ?c2) &*& c1 + c2 == count &*& c == c1 &*& (f == n ? true : malloc_block_node(f)) &*& (n == l ? true : malloc_block_node(n)) &*& c1 <= INT_MAX;
  {
    //@ open lseg(n, l, c2);
    struct node *next = n->next;
    //@ lseg_append_node(f);
    n = next;
    if (c == INT_MAX) abort();
    c = c + 1;
  }
  //@ open lseg(n, l, _);
  //@ lseg_to_nodes(f);
  //@ close llist(list, count);
  return c;
}

/*@
lemma void lseg_split(struct node *from, int i)
  requires lseg(from, ?to, ?count) &*& 0 <= i &*& i < count &*& (from == to ? true : malloc_block_node(from));
  ensures lseg(from, ?mid, i) &*& mid->next |-> ?next &*& mid->value |-> ?v &*& lseg(next, to, count - i - 1) &*& malloc_block_node(mid) &*& (from == mid ? true : malloc_block_node(from)) &*& (next == to ? true : malloc_block_node(next));
{
  open lseg(from, to, count);
  if (i == 0) {
    close lseg(from, from, 0);
  } else {
    lseg_split(from->next, i - 1);
    close lseg(from, ?mid, i);
  }
}

lemma void lseg_merge(struct node *from, struct node *mid)
  requires lseg(from, mid, ?c1) &*& mid->next |-> ?next &*& mid->value |-> ?v &*& lseg(next, ?to, ?c2) &*& malloc_block_node(mid) &*& (from == mid ? true : malloc_block_node(from)) &*& (next == to ? true : malloc_block_node(next));
  ensures lseg(from, to, c1 + c2 + 1) &*& (from == to ? true : malloc_block_node(from));
{
  open lseg(from, mid, c1);
  if (from == mid) {
    close lseg(next, to, c2);
    lseg_add(mid);
  } else {
    lseg_merge(from->next, mid);
    close lseg(from, to, c1 + c2 + 1);
  }
}
@*/

int llist_lookup(struct llist *list, int index)
  //@ requires llist(list, ?count) &*& 0 <= index &*& index < count;
  //@ ensures llist(list, count);
{
  //@ open llist(list, count);
  struct node *f = list->first;
  struct node *l = list->last;
  struct node *n = f;
  int i = 0;
  //@ nodes_to_lseg(f);
  while (i < index)
    //@ invariant lseg(f, n, i) &*& lseg(n, l, count - i) &*& 0 <= i &*& i <= index &*& index < count &*& (f == n ? true : malloc_block_node(f)) &*& (n == l ? true : malloc_block_node(n));
  {
    //@ open lseg(n, l, count - i);
    struct node *next = n->next;
    //@ lseg_append_node(f);
    n = next;
    i = i + 1;
  }
  //@ open lseg(n, l, count - i);
  int value = n->value;
  //@ close lseg(n->next, l, count - i - 1);
  //@ lseg_merge(f, n);
  //@ lseg_to_nodes(f);
  //@ close llist(list, count);
  return value;
}

int llist_removeFirst(struct llist *l)
  //@ requires llist(l, ?count) &*& count > 0;
  //@ ensures llist(l, count - 1);
{
  //@ open llist(l, count);
  struct node *nf = l->first;
  //@ open nodes(nf, ?last, count);
  struct node *nfn = nf->next;
  int nfv = nf->value;
  free(nf);
  l->first = nfn;
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
predicate iter(struct iter *i, struct node *cur) =
  i->current |-> cur &*& malloc_block_iter(i);

predicate llist_with_node(struct llist *l, int count, struct node *n, int idx) =
  l->first |-> ?f &*& l->last |-> ?last &*& malloc_block_llist(l) &*&
  last != 0 &*& last->next |-> _ &*& last->value |-> _ &*& malloc_block_node(last) &*&
  nodes(f, last, count);
@*/

struct iter *llist_create_iter(struct llist *l)
    //@ requires llist(l, ?count);
    //@ ensures llist(l, count) &*& iter(result, ?cur);
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
    //@ requires iter(i, ?cur) &*& cur->next |-> ?next &*& cur->value |-> ?v;
    //@ ensures iter(i, next) &*& cur->next |-> next &*& cur->value |-> v &*& result == v;
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
    //@ open llist(l, 3);
    //@ open nodes(_, _, 3);
    //@ open nodes(_, _, 2);
    //@ open nodes(_, _, 1);
    //@ open nodes(_, _, 0);
    //@ assert l->first |-> ?f &*& f->next |-> ?n1 &*& n1->next |-> ?n2 &*& n2->next |-> ?last;
    //@ close nodes(last, last, 0);
    struct iter *i1 = malloc(sizeof(struct iter));
    if (i1 == 0) abort();
    i1->current = l->first;
    //@ close iter(i1, f);
    struct iter *i2 = malloc(sizeof(struct iter));
    if (i2 == 0) abort();
    i2->current = l->first;
    //@ close iter(i2, f);
    int i1e1 = iter_next(i1); assert(i1e1 == 5);
    int i2e1 = iter_next(i2); assert(i2e1 == 5);
    int i1e2 = iter_next(i1); assert(i1e2 == 10);
    int i2e2 = iter_next(i2); assert(i2e2 == 10);
    //@ open iter(i1, _);
    free(i1);
    //@ open iter(i2, _);
    free(i2);
    //@ close nodes(n2, last, 1);
    //@ close nodes(n1, last, 2);
    //@ close nodes(f, last, 3);
    //@ close llist(l, 3);
    llist_dispose(l);
    return 0;
}