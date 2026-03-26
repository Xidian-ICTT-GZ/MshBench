#include "stdlib.h"
#include "limits.h"

struct node
{
  struct node *next;
  int value;
};

struct llist
{
  struct node *first;
  struct node *last;
};

struct iter
{
  struct node *current;
};

/*@
predicate node(struct node *n; struct node *next, int value) =
    n != 0 &*&
    n->next |-> next &*&
    n->value |-> value &*&
    malloc_block_node(n);

predicate lseg(struct node *from, struct node *to; list<int> vs) =
    from == to ?
        vs == nil
    :
        node(from, ?next, ?v) &*&
        lseg(next, to, ?vs0) &*&
        vs == cons(v, vs0);

predicate llist(struct llist *l; list<int> vs) =
    l != 0 &*&
    malloc_block_llist(l) &*&
    l->first |-> ?first &*&
    l->last |-> ?last &*&
    lseg(first, last, vs) &*&
    node(last, 0, _);

predicate iter(struct iter *i, struct node *current, struct node *last, list<int> vs) =
    i != 0 &*&
    malloc_block_iter(i) &*&
    i->current |-> current &*&
    lseg(current, last, vs) &*&
    node(last, 0, _);
@*/

/*@
lemma void lseg_add(struct node *from, struct node *to, struct node *newlast)
    requires lseg(from, to, ?vs) &*& node(to, newlast, ?v) &*& node(newlast, 0, _);
    ensures lseg(from, newlast, append(vs, cons(v, nil))) &*& node(newlast, 0, _);
{
    open lseg(from, to, vs);
    if (from == to) {
        close lseg(newlast, newlast, nil);
        close lseg(to, newlast, cons(v, nil));
    } else {
        lseg_add(_, to, newlast);
        close lseg(from, newlast, _);
    }
}
@*/

/*@
lemma void lseg_append(struct node *a, struct node *b, struct node *c)
    requires lseg(a, b, ?vs1) &*& lseg(b, c, ?vs2);
    ensures lseg(a, c, append(vs1, vs2));
{
    open lseg(a, b, vs1);
    if (a == b) {
    } else {
        lseg_append(_, b, c);
        close lseg(a, c, _);
    }
}
@*/

struct llist *create_llist()
//@ requires true;
//@ ensures llist(result, nil);
{
  struct llist *l = malloc(sizeof(struct llist));
  if (l == 0)
    abort();
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0)
    abort();
  l->first = n;
  l->last = n;
  //@ close lseg(n, n, nil);
  //@ close node(n, 0, 0);
  //@ close llist(l, nil);
  return l;
}

void llist_add(struct llist *list, int x)
//@ requires llist(list, ?vs);
//@ ensures llist(list, append(vs, cons(x, nil)));
{
  //@ open llist(list, vs);
  struct node *l = 0;
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0)
  {
    abort();
  }
  l = list->last;
  //@ open node(l, 0, _);
  l->next = n;
  l->value = x;
  list->last = n;
  //@ close node(l, n, x);
  //@ close node(n, 0, 0);
  //@ lseg_add(list->first, l, n);
  //@ close llist(list, append(vs, cons(x, nil)));
}

/*@
lemma void lseg_to_node(struct node *from, struct node *to)
    requires lseg(from, to, ?vs) &*& from != to;
    ensures node(from, ?next, ?v) &*& lseg(next, to, ?vs0) &*& vs == cons(v, vs0);
{
    open lseg(from, to, vs);
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

  //@ open node(l1, 0, _);
  //@ open lseg(f2, l2, vs2);
  if (f2 == l2)
  {
    //@ open node(l2, 0, _);
    free(l2);
    free(list2);
    //@ close node(l1, 0, _);
    //@ close llist(list1, vs1);
  }
  else
  {
    //@ open node(f2, ?f2next, ?f2val);
    l1->next = f2->next;
    l1->value = f2->value;
    list1->last = l2;
    free(f2);
    free(list2);
    //@ close node(l1, f2next, f2val);
    //@ lseg_add(list1->first, l1, l2);
    //@ lseg_append(list1->first, f2next, l2);
    //@ close llist(list1, append(vs1, vs2));
  }
}

void llist_dispose(struct llist *list)
//@ requires llist(list, ?vs);
//@ ensures true;
{
  //@ open llist(list, vs);
  struct node *n = list->first;
  struct node *l = list->last;
  //@ open node(l, 0, _);
  while (n != l)
  //@ invariant lseg(n, l, _) &*& l->next |-> 0 &*& l->value |-> _ &*& malloc_block_node(l) &*& malloc_block_llist(list);
  {
    //@ open lseg(n, l, _);
    //@ open node(n, _, _);
    struct node *next = n->next;
    free(n);
    n = next;
  }
  //@ open lseg(n, l, _);
  free(l);
  free(list);
}

/*@
lemma void lseg_length_positive(struct node *from, struct node *to)
    requires lseg(from, to, ?vs);
    ensures lseg(from, to, vs) &*& length(vs) >= 0;
{
    open lseg(from, to, vs);
    if (from == to) {
    } else {
        lseg_length_positive(_, to);
    }
    close lseg(from, to, vs);
}
@*/

int llist_length(struct llist *list)
//@ requires llist(list, ?vs);
//@ ensures llist(list, vs) &*& result == length(vs);
{
  //@ open llist(list, vs);
  struct node *f = list->first;
  struct node *n = f;
  struct node *l = list->last;
  int c = 0;
  //@ close lseg(f, n, nil);

  while (n != l)
  //@ invariant lseg(f, n, ?vs1) &*& lseg(n, l, ?vs2) &*& node(l, 0, _) &*& c == length(vs1) &*& vs == append(vs1, vs2) &*& malloc_block_llist(list) &*& list->first |-> f &*& list->last |-> l;
  {
    //@ open lseg(n, l, vs2);
    //@ open node(n, ?nnext, ?nval);
    struct node *next = n->next;
    //@ close node(n, nnext, nval);
    //@ lseg_add(f, n, nnext);
    //@ open lseg(nnext, nnext, _);
    n = next;
    if (c == INT_MAX)
      abort();
    c = c + 1;
    //@ append_assoc(vs1, cons(nval, nil), _);
  }
  //@ open lseg(n, l, _);
  //@ lseg_append(f, l, l);
  //@ close llist(list, vs);
  return c;
}

/*@
lemma void lseg_nth<t>(struct node *from, struct node *to, int i)
    requires lseg(from, to, ?vs) &*& 0 <= i &*& i < length(vs);
    ensures lseg(from, to, vs);
{
    open lseg(from, to, vs);
    if (i == 0) {
    } else {
        lseg_nth(_, to, i - 1);
    }
    close lseg(from, to, vs);
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
  //@ close lseg(f, n, nil);

  while (i < index)
  //@ invariant lseg(f, n, ?vs1) &*& lseg(n, l, ?vs2) &*& node(l, 0, _) &*& i == length(vs1) &*& vs == append(vs1, vs2) &*& i <= index &*& index < length(vs) &*& malloc_block_llist(list) &*& list->first |-> f &*& list->last |-> l;
  {
    //@ open lseg(n, l, vs2);
    //@ open node(n, ?nnext, ?nval);
    struct node *next = n->next;
    //@ close node(n, nnext, nval);
    //@ lseg_add(f, n, nnext);
    //@ open lseg(nnext, nnext, _);
    n = next;
    i = i + 1;
    //@ append_assoc(vs1, cons(nval, nil), _);
  }

  //@ open lseg(n, l, vs2);
  //@ open node(n, ?nnext, ?nval);
  int value = n->value;
  //@ close node(n, nnext, nval);
  //@ close lseg(n, l, vs2);
  //@ lseg_append(f, n, l);
  //@ close llist(list, vs);
  //@ nth_append_r(vs1, vs2, index - length(vs1));
  return value;
}

int llist_removeFirst(struct llist *l)
//@ requires llist(l, ?vs) &*& vs != nil;
//@ ensures llist(l, ?vs2) &*& vs == cons(result, vs2);
{
  //@ open llist(l, vs);
  struct node *nf = l->first;
  //@ open lseg(nf, ?last, vs);
  //@ open node(nf, ?nfnext, ?nfval);

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
  int x = llist_removeFirst(l2);
  assert(x == 40);
  llist_append(l1, l2);
  int n = llist_length(l1);
  assert(n == 5);
  int e0 = llist_lookup(l1, 0);
  assert(e0 == 10);
  int e1 = llist_lookup(l1, 1);
  assert(e1 == 20);
  int e2 = llist_lookup(l1, 2);
  assert(e2 == 30);
  int e3 = llist_lookup(l1, 3);
  assert(e3 == 50);
  int e4 = llist_lookup(l1, 4);
  assert(e4 == 60);
  llist_dispose(l1);
  return 0;
}

struct iter *llist_create_iter(struct llist *l)
//@ requires llist(l, ?vs);
//@ ensures iter(result, ?first, ?last, vs) &*& malloc_block_llist(l) &*& l->first |-> first &*& l->last |-> last;
{
  //@ open llist(l, vs);
  struct iter *i = 0;
  struct node *f = 0;

  i = malloc(sizeof(struct iter));
  if (i == 0)
  {
    abort();
  }

  f = l->first;
  i->current = f;
  //@ close iter(i, f, l->last, vs);
  return i;
}

int iter_next(struct iter *i)
//@ requires iter(i, ?current, ?last, ?vs) &*& vs != nil;
//@ ensures iter(i, ?next, last, tail(vs)) &*& result == head(vs);
{
  //@ open iter(i, current, last, vs);
  struct node *c = i->current;
  //@ open lseg(c, last, vs);
  //@ open node(c, ?cnext, ?cval);

  int value = c->value;
  struct node *n = c->next;

  i->current = n;
  //@ close node(c, cnext, cval);
  //@ close lseg(c, c, nil);
  //@ close iter(i, n, last, tail(vs));
  //@ leak lseg(c, c, nil);
  //@ leak node(c, _, _);
  return value;
}

void iter_dispose(struct iter *i)
//@ requires iter(i, ?current, ?last, ?vs);
//@ ensures lseg(current, last, vs) &*& node(last, 0, _);
{
  //@ open iter(i, current, last, vs);
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
  //@ assert iter(i1, ?f1, ?last1, ?vs1);
  //@ assert malloc_block_llist(l) &*& l->first |-> f1 &*& l->last |-> last1;
  struct iter *i2 = malloc(sizeof(struct iter));
  if (i2 == 0) abort();
  //@ open iter(i1, f1, last1, vs1);
  i2->current = f1;
  //@ close iter(i1, f1, last1, vs1);
  //@ close lseg(f1, f1, nil);
  //@ close iter(i2, f1, last1, nil);
  //@ leak iter(i2, _, _, _);
  int i1e1 = iter_next(i1);
  assert(i1e1 == 5);
  int i1e2 = iter_next(i1);
  assert(i1e2 == 10);
  iter_dispose(i1);
  //@ leak lseg(_, _, _);
  //@ leak node(_, _, _);
  //@ leak malloc_block_llist(l);
  //@ leak l->first |-> _;
  //@ leak l->last |-> _;
  //@ leak malloc_block_iter(i2);
  //@ leak i2->current |-> _;
  return 0;
}