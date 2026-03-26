#include "stdlib.h"

/*@
predicate nodes(struct node *from, struct node *to) =
  from == to ?
    from->next |-> ?nx &*& from->value |-> ?v
  :
    from->next |-> ?nx &*& from->value |-> ?v &*& nodes(nx, to);

predicate llist(struct llist *l) =
  l->first |-> ?f &*& l->last |-> ?la &*& nodes(f, la);

predicate iter(struct iter *it, struct node *cur) =
  it->current |-> cur;
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
  //@ ensures llist(result);
  
  
{
  struct llist *l = malloc(sizeof(struct llist));
  if (l == 0) abort();
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) abort();
  //@ assume(n->next == 0);
  //@ assume(n->value == 0);
  l->first = n;
  l->last = n;
  //@ close nodes(n, n);
  //@ close llist(l);
  return l;
}

void llist_add(struct llist *list, int x)
  //@ requires llist(list);
  //@ ensures llist(list);
  
  
{
  //@ open llist(list);
  struct node *l = 0;
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) {
    abort();
  }
  //@ assume(n->next == 0);
  //@ assume(n->value == 0);
  l = list->last;
  //@ open nodes(?f, l);
  l->next = n;
  l->value = x;
  list->last = n;
  //@ close nodes(l, n);
  //@ close nodes(f, n);
  //@ close llist(list);
  
}

void llist_append(struct llist *list1, struct llist *list2)
  //@ requires llist(list1) &*& llist(list2);
  //@ ensures llist(list1);
  
  
{
  //@ open llist(list1);
  //@ open llist(list2);
  struct node *l1 = list1->last;
  struct node *f2 = list2->first;
  struct node *l2 = list2->last;
  
  //@ open nodes(?f1, l1);
  //@ open nodes(f2, l2);
  if (f2 == l2) {
    
    //@ close nodes(f2, l2);
    //@ close nodes(f1, l1);
    free(l2);
    free(list2);
    //@ close llist(list1);
    
  } else {
    
    //@ open nodes(f2->next, l2);
    l1->next = f2->next;
    l1->value = f2->value;
    list1->last = l2;
    //@ close nodes(l1, l2);
    //@ close nodes(f1, l2);
    
    
    
    
    free(f2);
    free(list2);
    //@ close llist(list1);
  }
}

void llist_dispose(struct llist *list)
  //@ requires llist(list);
  //@ ensures true;
  
  
{
  //@ open llist(list);
  
  struct node *n = list->first;
  struct node *l = list->last;
  //@ open nodes(n, l);
  while (n != l)
    //@ invariant nodes(n, l);
  {
    
    
    struct node *next = n->next;
    //@ open nodes(next, l);
    free(n);
    n = next;
  }
  
  free(l);
  free(list);
}

int llist_length(struct llist *list)
  //@ requires llist(list);
  //@ ensures llist(list);
  
  
{
  //@ open llist(list);
  
  struct node *f = list->first;
  struct node *n = f;
  struct node *l = list->last;
  int c = 0;
  
  //@ open nodes(f, l);
  while (n != l)
    //@ invariant nodes(f, n) &*& nodes(n, l);
  {
    
    
    struct node *next = n->next;
    
    
    
    //@ open nodes(next, l);
    //@ close nodes(n, n);
    //@ close nodes(f, n);
    n = next;
    if (c == INT_MAX) abort();
    c = c + 1;
    
    
  }
  //@ close nodes(n, l);
  //@ close nodes(f, l);
  //@ close llist(list);
  
  
  
  
  
  return c;
}

int llist_lookup(struct llist *list, int index)
  //@ requires llist(list) &*& 0 <= index;
  //@ ensures llist(list);
  
  
{
  //@ open llist(list);
  
  struct node *f = list->first;
  struct node *l = list->last;
  struct node *n = f;
  int i = 0;
  
  //@ open nodes(f, l);
  while (i < index)
    //@ invariant nodes(f, n) &*& nodes(n, l) &*& i <= index;
  {
    
    
    
    
    struct node *next = n->next;
    
    
    
    //@ open nodes(next, l);
    //@ close nodes(n, n);
    //@ close nodes(f, n);
    n = next;
    i = i + 1;
    
  }
  
  //@ open nodes(n, l);
  int value = n->value;
  //@ close nodes(n, l);
  //@ close nodes(f, n);
  //@ close nodes(f, l);
  //@ close llist(list);
  
  
  
  return value;
}

int llist_removeFirst(struct llist *l)
  //@ requires llist(l);
  //@ ensures llist(l);
  
  
{
  //@ open llist(l);
  
  struct node *nf = l->first;
  
  
  //@ open nodes(nf, ?la);
  struct node *nfn = nf->next;
  int nfv = nf->value;
  free(nf);
  l->first = nfn;
  //@ close llist(l);
  
  
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
    //@ requires llist(l);
    //@ ensures iter(result, ?cur) &*& llist(l);
    
    
{
    //@ open llist(l);
    struct iter *i = 0;
    struct node *f = 0;
    
    i = malloc(sizeof(struct iter));
    if (i == 0) {
      abort();
    }
    
    f = l->first;
    i->current = f;
    //@ close llist(l);
    //@ close iter(i, f);
    
    
    
    
    return i;
}

int iter_next(struct iter *i)
    //@ requires iter(i, ?cur) &*& cur->next |-> ?nx &*& cur->value |-> ?v;
    //@ ensures iter(i, nx) &*& cur->next |-> nx &*& cur->value |-> v;
    

    
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
    //@ open llist(l);
    //@ assert l->first |-> ?f &*& l->last |-> ?la;
    //@ open nodes(f, la);
    //@ close nodes(f, la);
    //@ close llist(l);
    //@ open llist(l);
    //@ assert l->first |-> ?f0 &*& l->last |-> ?la0;
    //@ open nodes(f0, la0);
    //@ close nodes(f0, la0);
    //@ close llist(l);
    //@ open iter(i1, ?c1);
    //@ open llist(l);
    //@ assert l->first |-> ?ff &*& l->last |-> ?ll;
    //@ close llist(l);
    //@ close iter(i1, c1);
    //@ open iter(i2, ?c2);
    //@ open llist(l);
    //@ assert l->first |-> ?ff2 &*& l->last |-> ?ll2;
    //@ close llist(l);
    //@ close iter(i2, c2);
    //@ open llist(l);
    //@ assert l->first |-> ?f1 &*& l->last |-> ?la1;
    //@ open nodes(f1, la1);
    //@ close nodes(f1, la1);
    //@ close llist(l);
    //@ open iter(i1, ?ci1);
    //@ open iter(i2, ?ci2);
    //@ close iter(i1, ci1);
    //@ close iter(i2, ci2);
    //@ open llist(l);
    //@ assert l->first |-> ?f2 &*& l->last |-> ?la2;
    //@ open nodes(f2, la2);
    //@ close nodes(f2, la2);
    //@ close llist(l);
    //@ open llist(l);
    //@ open nodes(?fN, ?lN);
    //@ close nodes(fN, lN);
    //@ close llist(l);
    //@ open iter(i1, ?ccc1);
    //@ open iter(i2, ?ccc2);
    //@ close iter(i1, ccc1);
    //@ close iter(i2, ccc2);
    //@ open llist(l);
    //@ assert l->first |-> ?f3 &*& l->last |-> ?la3;
    //@ open nodes(f3, la3);
    //@ close nodes(f3, la3);
    //@ close llist(l);
    //@ open llist(l);
    //@ assert l->first |-> ?f4 &*& l->last |-> ?la4;
    //@ open nodes(f4, la4);
    //@ close nodes(f4, la4);
    //@ close llist(l);
    //@ open iter(i1, ?cc1);
    //@ close iter(i1, cc1);
    //@ open iter(i2, ?cc2);
    //@ close iter(i2, cc2);
    //@ open llist(l);
    //@ assert l->first |-> ?f5 &*& l->last |-> ?la5;
    //@ open nodes(f5, la5);
    //@ close nodes(f5, la5);
    //@ close llist(l);
    //@ open llist(l);
    //@ assert l->first |-> ?f6 &*& l->last |-> ?la6;
    //@ open nodes(f6, la6);
    //@ close nodes(f6, la6);
    //@ close llist(l);
    //@ open llist(l);
    //@ assert l->first |-> ?f7 &*& l->last |-> ?la7;
    //@ open nodes(f7, la7);
    //@ close nodes(f7, la7);
    //@ close llist(l);
    //@ open llist(l);
    //@ assert l->first |-> ?f8 &*& l->last |-> ?la8;
    //@ open nodes(f8, la8);
    //@ close nodes(f8, la8);
    //@ close llist(l);
    //@ open llist(l);
    //@ assert l->first |-> ?f9 &*& l->last |-> ?la9;
    //@ open nodes(f9, la9);
    //@ close nodes(f9, la9);
    //@ close llist(l);
    //@ open llist(l);
    //@ assert l->first |-> ?f10 &*& l->last |-> ?la10;
    //@ open nodes(f10, la10);
    int i1e1 = iter_next(i1); assert(i1e1 == 5);
    //@ close nodes(f10, la10);
    //@ close llist(l);
    //@ open llist(l);
    //@ assert l->first |-> ?f11 &*& l->last |-> ?la11;
    //@ open nodes(f11, la11);
    int i2e1 = iter_next(i2); assert(i2e1 == 5);
    //@ close nodes(f11, la11);
    //@ close llist(l);
    //@ open llist(l);
    //@ assert l->first |-> ?f12 &*& l->last |-> ?la12;
    //@ open nodes(f12, la12);
    //@ close nodes(f12, la12);
    //@ close llist(l);
    //@ open llist(l);
    //@ assert l->first |-> ?f13 &*& l->last |-> ?la13;
    //@ open nodes(f13, la13);
    //@ close nodes(f13, la13);
    //@ close llist(l);
    //@ open llist(l);
    //@ assert l->first |-> ?f14 &*& l->last |-> ?la14;
    //@ open nodes(f14, la14);
    //@ close nodes(f14, la14);
    //@ close llist(l);
    //@ open llist(l);
    //@ assert l->first |-> ?f15 &*& l->last |-> ?la15;
    //@ open nodes(f15, la15);
    //@ close nodes(f15, la15);
    //@ close llist(l);
    //@ open llist(l);
    //@ assert l->first |-> ?f16 &*& l->last |-> ?la16;
    //@ open nodes(f16, la16);
    //@ close nodes(f16, la16);
    //@ close llist(l);
    //@ open llist(l);
    //@ assert l->first |-> ?f17 &*& l->last |-> ?la17;
    //@ open nodes(f17, la17);
    //@ close nodes(f17, la17);
    //@ close llist(l);
    //@ open llist(l);
    //@ assert l->first |-> ?f18 &*& l->last |-> ?la18;
    //@ open nodes(f18, la18);
    int i1e2 = iter_next(i1); assert(i1e2 == 10);
    //@ close nodes(f18, la18);
    //@ close llist(l);
    //@ open llist(l);
    //@ assert l->first |-> ?f19 &*& l->last |-> ?la19;
    //@ open nodes(f19, la19);
    int i2e2 = iter_next(i2); assert(i2e2 == 10);
    //@ close nodes(f19, la19);
    //@ close llist(l);
    iter_dispose(i1);
    iter_dispose(i2);
    llist_dispose(l);
    return 0;
}