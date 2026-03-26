#include "stdlib.h"

/*@ predicate node(struct node *n; struct node *next, int value) =
    n != 0 &*&
    malloc_block_node(n) &*&
    n->next |-> next &*&
    n->value |-> value;
@*/

/*@ predicate llist(struct llist *l; list<struct node *> nodes) =
    l != 0 &*&
    malloc_block_llist(l) &*&
    l->first |-> ?first &*&
    l->last |-> ?last &*&
    nodes == cons(first, ?rest) &*&
    length(nodes) >= 1 &*&
    node(first, ?n1, _) &*&
    llist_nodes(rest, first, last);
@*/

/*@ predicate llist_nodes(list<struct node *> nodes, struct node *prev, struct node *last) =
    switch (nodes) {
        case nil: return prev == last;
        case cons(h, t): return node(prev, h, _) &*& llist_nodes(t, h, last);
    };
@*/

/*@ predicate iter(struct iter *i; struct node *current) =
    i != 0 &*&
    malloc_block_iter(i) &*&
    i->current |-> current;
@*/

//@ #include <list.gh>

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
//@ ensures llist(result, ?nodes) &*& length(nodes) == 1;
{
  struct llist *l = malloc(sizeof(struct llist));
  if (l == 0) abort();
  //@ close malloc_block_llist(l);
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) abort();
  //@ close node(n, 0, 0);
  l->first = n;
  l->last = n;
  //@ close llist_nodes(nil, n, n);
  //@ close llist(l, cons(n, nil));
  return l;
}

void llist_add(struct llist *list, int x)
//@ requires llist(list, ?old_nodes) &*& length(old_nodes) >= 1;
//@ ensures llist(list, ?new_nodes) &*& length(new_nodes) == length(old_nodes) + 1;
{
  struct node *l = 0;
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) {
    abort();
  }
  //@ close node(n, 0, 0);
  l = list->last;
  //@ open llist(list, old_nodes);
  //@ assert llist_nodes(?rest, ?prev, l);
  l->next = n;
  l->value = x;
  list->last = n;
  //@ close llist_nodes(cons(n, nil), l, n);
  //@ close llist_nodes(append(rest, cons(l, nil)), prev, l); // Not needed; instead:
  //@ close llist_nodes(cons(n, nil), l, n);
  //@ close llist(list, append(take(length(old_nodes)-1, old_nodes), cons(l, cons(n, nil))));
  
  //@ close llist(list, append(butlast(old_nodes), cons(l, cons(n, nil))));
  
  //@ open llist_nodes(rest, prev, l);
  //@ close llist_nodes(cons(n, nil), l, n);
  //@ close llist(list, append(old_nodes, cons(n, nil)));
}

void llist_append(struct llist *list1, struct llist *list2)
//@ requires llist(list1, ?nodes1) &*& llist(list2, ?nodes2) &*& length(nodes2) >= 1;
//@ ensures llist(list1, ?result_nodes) &*& length(result_nodes) == length(nodes1) + length(nodes2) - 1;
{
  struct node *l1 = list1->last;
  struct node *f2 = list2->first;
  struct node *l2 = list2->last;
  
  //@ open llist(list1, nodes1);
  //@ open llist(list2, nodes2);
  //@ assert llist_nodes(?rest1, ?prev1, l1);
  //@ assert llist_nodes(?rest2, f2, l2);
  
  if (f2 == l2) {
    //@ open node(f2, _, _);
    //@ open malloc_block_node(f2);
    free(l2);
    //@ open malloc_block_llist(list2);
    free(list2);
    //@ close llist(list1, nodes1);
  } else {
    l1->next = f2->next;
    l1->value = f2->value;
    list1->last = l2;
    
    //@ open node(f2, _, _);
    //@ open malloc_block_node(f2);
    free(f2);
    //@ open malloc_block_llist(list2);
    free(list2);
    //@ close llist(list1, append(butlast(nodes1), tail(nodes2)));
    
    //@ close llist(list1, append(nodes1, tail(nodes2)));
  }
}

void llist_dispose(struct llist *list)
//@ requires llist(list, ?nodes);
//@ ensures true;
{
  struct node *n = list->first;
  struct node *l = list->last;
  //@ open llist(list, nodes);
  //@ assert llist_nodes(?rest, n, l);
  while (n != l)
  //@ invariant llist_nodes(?curr_rest, n, l) &*& malloc_block_llist(list);
  {
    struct node *next = n->next;
    //@ open node(n, next, _);
    //@ open malloc_block_node(n);
    free(n);
    n = next;
  }
  
  //@ open node(l, _, _);
  //@ open malloc_block_node(l);
  free(l);
  //@ open malloc_block_llist(list);
  free(list);
}

int llist_length(struct llist *list)
//@ requires llist(list, ?nodes);
//@ ensures llist(list, nodes) &*& result == length(nodes) - 1;
{
  struct node *f = list->first;
  struct node *n = f;
  struct node *l = list->last;
  int c = 0;
  
  //@ open llist(list, nodes);
  //@ assert llist_nodes(?rest, f, l);
  //@ close llist(list, nodes);
  
  while (n != l)
  //@ invariant llist(list, nodes) &*& mem(n, nodes) == true &*& c == length(take_while((node*)n != _, nodes)) - 1;
  //@ invariant 0 <= c;
  {
    struct node *next = n->next;
    n = next;
    if (c == INT_MAX) abort();
    c = c + 1;
  }
  
  return c;
}

int llist_lookup(struct llist *list, int index)
//@ requires llist(list, ?nodes) &*& 0 <= index &*& index < length(nodes) - 1;
//@ ensures llist(list, nodes) &*& result == nth(index + 1, nodes, _)->value;
{
  struct node *f = list->first;
  struct node *l = list->last;
  struct node *n = f;
  int i = 0;
  //@ open llist(list, nodes);
  //@ close llist(list, nodes);
  while (i < index)
  //@ invariant llist(list, nodes) &*& 0 <= i &*& i <= index &*& n == nth(i, nodes, _);
  {
    struct node *next = n->next;
    n = next;
    i = i + 1;
  }
  
  int value = n->value;
  return value;
}

int llist_removeFirst(struct llist *l)
//@ requires llist(l, ?nodes) &*& length(nodes) >= 2;
//@ ensures llist(l, tail(nodes)) &*& result == head(nodes)->value;
{
  struct node *nf = l->first;
  //@ open llist(l, nodes);
  //@ assert node(nf, ?nfn, ?nfv);
  struct node *nfn = nf->next;
  int nfv = nf->value;
  //@ open malloc_block_node(nf);
  free(nf);
  l->first = nfn;
  //@ close llist(l, tail(nodes));
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
  //@ assert x1 == 10;
  int x2 = llist_removeFirst(l);
  //@ assert x2 == 20;
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
  int x = llist_removeFirst(l2); //@ assert(x == 40);
  llist_append(l1, l2);
  int n = llist_length(l1); //@ assert(n == 5);
  int e0 = llist_lookup(l1, 0); //@ assert(e0 == 10);
  int e1 = llist_lookup(l1, 1); //@ assert(e1 == 20);
  int e2 = llist_lookup(l1, 2); //@ assert(e2 == 30);
  int e3 = llist_lookup(l1, 3); //@ assert(e3 == 50);
  int e4 = llist_lookup(l1, 4); //@ assert(e4 == 60);
  llist_dispose(l1);
  return 0;
}

struct iter {
    struct node *current;
};

struct iter *llist_create_iter(struct llist *l)
//@ requires llist(l, ?nodes);
//@ ensures llist(l, nodes) &*& iter(result, ?current) &*& current == head(nodes);
{
    struct iter *i = 0;
    struct node *f = 0;
    i = malloc(sizeof(struct iter));
    if (i == 0) {
      abort();
    }
    //@ close malloc_block_iter(i);
    f = l->first;
    i->current = f;
    //@ close iter(i, f);
    return i;
}

int iter_next(struct iter *i)
//@ requires iter(i, ?current) &*& current != 0 &*& node(current, ?next, ?value);
//@ ensures iter(i, next) &*& result == value;
{
    struct node *c = i->current;
    //@ open iter(i, current);
    //@ assert node(c, ?n, ?v);
    int value = c->value;
    struct node *n = c->next;
    i->current = n;
    //@ close iter(i, n);
    return value;
}

void iter_dispose(struct iter *i)
//@ requires iter(i, ?current);
//@ ensures true;
{
    //@ open iter(i, current);
    //@ open malloc_block_iter(i);
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
    int i1e1 = iter_next(i1); //@ assert(i1e1 == 5);
    int i2e1 = iter_next(i2); //@ assert(i2e1 == 5);
    int i1e2 = iter_next(i1); //@ assert(i1e2 == 10);
    int i2e2 = iter_next(i2); //@ assert(i2e2 == 10);
    iter_dispose(i1);
    iter_dispose(i2);
    llist_dispose(l);
    return 0;
}