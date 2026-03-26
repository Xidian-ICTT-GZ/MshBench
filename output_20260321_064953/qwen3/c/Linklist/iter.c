#include "stdlib.h"

/*@ predicate node(struct node *n; struct node *next, int value) =
      n != 0 &*&
      malloc_block_node(n) &*&
      n->next |-> next &*&
      n->value |-> value;
@*/

/*@ predicate llist(struct llist *l; struct node *first, struct node *last) =
      l != 0 &*&
      malloc_block_llist(l) &*&
      l->first |-> first &*&
      l->last |-> last;
@*/

/*@ predicate iter(struct iter *i; struct node *current) =
      i != 0 &*&
      malloc_block_iter(i) &*&
      i->current |-> current;
@*/

struct node {
  struct node *next;
  int value;
};

struct llist {
  struct node *first;
  struct node *last;
};

/*@ requires true;
    ensures llist(result, ?first, ?last) &*& node(first, 0, _) &*& first == last;
@*/
struct llist *create_llist()
  
  
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

/*@ requires llist(list, ?first, ?last) &*& node(last, 0, _);
    ensures llist(list, first, ?new_last) &*& node(new_last, 0, _) &*& node(last, new_last, x);
@*/
void llist_add(struct llist *list, int x)
  
  
{
  struct node *l = 0;
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) {
    abort();
  }
  //@ close node(n, 0, 0);
  l = list->last;
  //@ open llist(list, _, _);
  //@ open node(l, _, _);
  l->next = n;
  l->value = x;
  list->last = n;
  //@ close node(l, n, x);
  //@ close llist(list, _, n);
  
}

/*@ requires llist(list1, ?f1, ?l1) &*& node(l1, 0, _) &*&
            llist(list2, ?f2, ?l2) &*& node(f2, ?nf2, ?vf2) &*&
            (f2 == l2 ? true : node(l2, 0, _) &*& nodes_in_between(f2, l2)) &*& f2 != 0;
    ensures llist(list1, f1, l2) &*& (f2 == l2 ? true : node(l1, nf2, vf2) &*& nodes_in_between(nf2, l2));
@*/
void llist_append(struct llist *list1, struct llist *list2)
  
  
{
  struct node *l1 = list1->last;
  struct node *f2 = list2->first;
  struct node *l2 = list2->last;
  
  //@ open llist(list1, _, _);
  //@ open llist(list2, _, _);
  if (f2 == l2) {
    //@ open node(f2, _, _);
    free(l2);
    free(list2);
    //@ close llist(list1, _, l1);
  } else {
    //@ open node(f2, ?nf2, ?vf2);
    l1->next = f2->next;
    l1->value = f2->value;
    list1->last = l2;
    //@ close node(l1, nf2, vf2);
    //@ close llist(list1, _, l2);
    free(f2);
    free(list2);
  }
}

/*@ predicate nodes_in_between(struct node *start, struct node *end) =
      start != end &*& node(start, ?next, _) &*&
      (next == end ? true : nodes_in_between(next, end));
@*/

void llist_dispose(struct llist *list)
  
  
{
  //@ open llist(list, ?first, ?last);
  struct node *n = list->first;
  struct node *l = list->last;
  while (n != l)
    
  {
    //@ open node(n, ?next, _);
    struct node *next = n->next;
    free(n);
    n = next;
  }
  //@ open node(l, _, _);
  free(l);
  free(list);
}

/*@ requires llist(list, ?first, ?last) &*& (first == last ? true : nodes_in_between(first, last));
    ensures true;
@*/
int llist_length(struct llist *list)
  
  
{
  //@ open llist(list, ?f, ?l);
  struct node *f = list->first;
  struct node *n = f;
  struct node *l = list->last;
  int c = 0;
  
  while (n != l)
    
  {
    //@ if (n != l) open node(n, ?next, _);
    struct node *next = n->next;
    n = next;
    if (c == INT_MAX) abort();
    c = c + 1;
  }
  //@ if (f != l) close llist(list, f, l);
  return c;
}

/*@ requires llist(list, ?first, ?last) &*& (first == last ? index == 0 : (index >= 0 &*& nodes_up_to(first, last, index)));
    ensures true;
@*/
int llist_lookup(struct llist *list, int index)
  
  
{
  //@ open llist(list, ?f, ?l);
  struct node *f = list->first;
  struct node *l = list->last;
  struct node *n = f;
  int i = 0;
  
  while (i < index)
    
  {
    //@ open node(n, ?next, _);
    struct node *next = n->next;
    n = next;
    i = i + 1;
  }
  //@ open node(n, _, ?value);
  int value = n->value;
  //@ close node(n, _, value);
  //@ close llist(list, f, l);
  return value;
}

/*@ predicate nodes_up_to(struct node *start, struct node *end, int count) =
      count == 0 ? start == end :
      start != end &*& node(start, ?next, _) &*&
      (count == 1 ? next == end : nodes_up_to(next, end, count - 1));
@*/

/*@ requires llist(l, ?first, ?last) &*& node(first, ?nfn, ?nfv) &*& first != last;
    ensures llist(l, nfn, last) &*& result == nfv;
@*/
int llist_removeFirst(struct llist *l)
  
  
{
  //@ open llist(l, ?first, ?last);
  struct node *nf = l->first;
  //@ open node(nf, ?nfn, ?nfv);
  struct node *nfn = nf->next;
  int nfv = nf->value;
  free(nf);
  l->first = nfn;
  //@ close llist(l, nfn, last);
  return nfv;
}

/*@ requires true;
    ensures true;
@*/
void main0()
  
  
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

/*@ requires true;
    ensures true;
@*/
int main() 
  
  
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

/*@ requires llist(l, ?first, ?last) &*& (first == last ? true : nodes_in_between(first, last));
    ensures iter(result, first);
@*/
struct iter *llist_create_iter(struct llist *l)
    
    
{
    struct iter *i = 0;
    struct node *f = 0;
    
    i = malloc(sizeof(struct iter));
    if (i == 0) {
      abort();
    }
    //@ close iter(i, _);
    f = l->first;
    i->current = f;
    //@ close iter(i, f);
    return i;
}

/*@ requires iter(i, ?current) &*& node(current, ?next, ?value);
    ensures iter(i, next) &*& result == value;
@*/
int iter_next(struct iter *i)
    

    
{
    //@ open iter(i, ?c);
    struct node *c = i->current;
    //@ open node(c, ?n, ?value);
    int value = c->value;
    struct node *n = c->next;
    i->current = n;
    //@ close iter(i, n);
    return value;
}

/*@ requires iter(i, _);
    ensures true;
@*/
void iter_dispose(struct iter *i)
    
    
{
    //@ open iter(i, _);
    free(i);
}

/*@ requires true;
    ensures true;
@*/
int main2()
    
    
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