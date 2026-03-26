#include "stdlib.h"

struct node {
  struct node *next;
  int value;
};
/*@ 
predicate node(struct node *n; int v, struct node *next) = 
  n->value |-> v &*& n->next |-> next;
@*/

struct llist {
  struct node *first;
  struct node *last;
};
/*@ 
predicate llist(struct llist *l; struct node *first, struct node *last) = 
  l->first |-> first &*& l->last |-> last;
@*/

/*@ 
predicate nodes(struct node *start, struct node *end; list<int> vs) = 
  start == end ? vs == nil : 
    start != 0 &*& node(start, head(vs), ?next) &*& nodes(next, end, tail(vs));
@*/

struct llist *create_llist()
  //@ requires true;
  //@ ensures llist(result, ?f, ?l) &*& nodes(f, l, nil);
  
{
  struct llist *l = malloc(sizeof(struct llist));
  if (l == 0) abort();
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) abort();
  l->first = n;
  l->last = n;
  //@ close node(n, 0, 0);
  //@ close llist(l, n, n);
  return l;
}

void llist_add(struct llist *list, int x)
  //@ requires llist(list, ?f, ?l) &*& nodes(f, l, ?vs);
  //@ ensures llist(list, f, ?newLast) &*& nodes(f, newLast, append(vs, cons(x, nil)));
  
{
  struct node *l = 0;
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) {
    abort();
  }
  l = list->last;
  //@ open llist(list, f, l);
  //@ open nodes(f, l, vs);
  //@ open node(l, ?lv, 0);
  l->next = n;
  l->value = x;
  list->last = n;
  //@ close node(l, x, n);
  //@ close node(n, 0, 0);
  //@ close nodes(f, n, append(vs, cons(x, nil)));
  //@ close llist(list, f, n);
 
}

void llist_append(struct llist *list1, struct llist *list2)
  //@ requires llist(list1, ?f1, ?l1) &*& llist(list2, ?f2, ?l2) &*& nodes(f1, l1, ?vs1) &*& nodes(f2, l2, ?vs2);
  //@ ensures llist(list1, f1, ?newLast) &*& nodes(f1, newLast, append(vs1, vs2)) &*& true;
  
{
  struct node *l1 = list1->last;
  struct node *f2 = list2->first;
  struct node *l2 = list2->last;
  //@ open llist(list1, f1, l1);
  //@ open nodes(f1, l1, vs1);
  //@ open llist(list2, f2, l2);
  //@ open nodes(f2, l2, vs2);
  if (f2 == l2) {
    //@ open node(l2, ?val, ?next);
    //@ close nodes(f2, l2, nil);
    free(l2);
    free(list2);
    //@ close nodes(f1, l1, vs1);
    //@ close llist(list1, f1, l1);
  } else {
    //@ open node(f2, ?fv, ?fn);
    l1->next = f2->next;
    l1->value = f2->value;
    list1->last = l2;
    //@ close nodes(f1, l2, append(append(take(length(vs1)-1, vs1), cons(fv, nil)), tail(vs2)));
    free(f2);
    free(list2);
    //@ close llist(list1, f1, l2);
  }
}

void llist_dispose(struct llist *list)
  //@ requires llist(list, ?f, ?l) &*& nodes(f, l, ?vs);
  //@ ensures true;
  
{
  struct node *n = list->first;
  struct node *l = list->last;
  //@ open llist(list, f, l);
  //@ open nodes(f, l, vs);
  while (n != l)
    //@ invariant nodes(n, l, ?vss);
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
  //@ requires llist(list, ?f, ?l) &*& nodes(f, l, ?vs);
  //@ ensures llist(list, f, l) &*& nodes(f, l, vs) &*& result == length(vs);
  
{
  struct node *f = list->first;
  struct node *n = f;
  struct node *l = list->last;
  int c = 0;
  //@ open llist(list, f, l);
  //@ open nodes(f, l, vs);
  while (n != l)
    //@ invariant nodes(n, l, ?vss) &*& llist(list, f, l) &*& c == length(vs)-length(vss);
  {
    struct node *next = n->next;
    n = next;
    if (c == INT_MAX) abort();
    c = c + 1;
  }
  //@ close nodes(n, l, nil);
  //@ close llist(list, f, l);
  return c;
}

int llist_lookup(struct llist *list, int index)
  //@ requires llist(list, ?f, ?l) &*& nodes(f, l, ?vs) &*& 0 <= index &*& index < length(vs);
  //@ ensures llist(list, f, l) &*& nodes(f, l, vs) &*& result == nth(index, vs);
  
{
  struct node *f = list->first;
  struct node *l = list->last;
  struct node *n = f;
  int i = 0;
  //@ open llist(list, f, l);
  //@ open nodes(f, l, vs);
  while (i < index)
    //@ invariant nodes(n, l, ?vss) &*& llist(list, f, l) &*& i <= index &*& i <= length(vs);
  {
    struct node *next = n->next;
    n = next;
    i = i + 1;
  }
  //@ open node(n, ?val, ?next);
  //@ close nodes(n, l, cons(val, tail(vs)));
  //@ close llist(list, f, l);
  int value = n->value;
  return value;
}

int llist_removeFirst(struct llist *l)
  //@ requires llist(l, ?f, ?la) &*& nodes(f, la, cons(?v, ?vs));
  //@ ensures llist(l, ?newf, la) &*& nodes(newf, la, vs) &*& result == v;
{
  struct node *nf = l->first;
  //@ open llist(l, f, la);
  //@ open nodes(f, la, cons(v, vs));
  //@ open node(nf, v, ?next);
  
  struct node *nfn = nf->next;
  int nfv = nf->value;
  free(nf);
  l->first = nfn;
  //@ close llist(l, nfn, la);
  //@ close nodes(nfn, la, vs);
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
predicate iter(struct iter *it; struct node *current) = 
  it->current |-> current;
@*/

struct iter *llist_create_iter(struct llist *l)
  //@ requires llist(l, ?f, ?l2) &*& nodes(f, l2, ?vs);
  //@ ensures iter(result, f);
    
{
    struct iter *i = 0;
    struct node *f = 0;
    //@ open llist(l, f, l2);
    
    i = malloc(sizeof(struct iter));
    if (i == 0) {
      abort();
    }
    
    f = l->first;
    i->current = f;
    //@ close iter(i, f);
    //@ close llist(l, f, l2);
    return i;
}

int iter_next(struct iter *i)
  //@ requires iter(i, ?c) &*& c != 0 &*& node(c, ?v, ?n);
  //@ ensures iter(i, n) &*& result == v;
{
    struct node *c = i->current;
    //@ open iter(i, c);
    //@ open node(c, ?value, ?next);
    
    int value = c->value;
    struct node *n = c->next;
    
    i->current = n;
    //@ close iter(i, n);
    return value;
}

void iter_dispose(struct iter *i)
  //@ requires iter(i, ?c);
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