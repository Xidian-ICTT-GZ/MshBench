#include "stdlib.h"

struct node {
  void* val;
  struct node* next;
};

/*@ predicate nodes(struct node* n; list<void*> vals) =
      n == 0 ?
         emp
      :
         n->val |-> ?v &*& n->next |-> ?nx &*& malloc_block_node(n) &*&
         nodes(nx, ?tail) &*& vals == cons(v, tail);
@*/

struct set {
  struct node* head;
};

/*@ predicate set(struct set* s; list<void*> vals) =
      s->head |-> ?h &*& malloc_block_set(s) &*& nodes(h, vals);
@*/

struct set* create_set()
  
//@ requires true;
//@ ensures result == 0 ? true : set(result, nil);
{
  struct set* set = malloc(sizeof(struct set));
  if(set == 0) return 0;
  set->head = 0;
  
  return set;
}

void set_add(struct set* set, void* x)
  
//@ requires set(set, ?vals);
//@ ensures set(set, cons(x, vals));
{
  struct node* n = malloc(sizeof(struct node));
  if(n == 0) abort();
  n->next = set->head;
  n->val = x;
  set->head = n;
  
}

bool set_contains(struct set* set, void* x)
  
//@ requires set(set, ?vals);
//@ ensures set(set, vals) &*& result == existsb((eq_voidptr)(x), vals);
{
  struct node* curr = set->head;
  bool found = false;
  
  
  //@ open set(set, vals);
  //@ open nodes(curr, ?l);
  
  while(curr != 0 && !found) 
    //@ invariant nodes(curr, ?l1) &*& set->head |-> ?h &*& malloc_block_set(set) &*& set != 0 &*& 
    //@  append(l1, ?l2) == vals &*& found == existsb((eq_voidptr)(x), take(length(l1), vals));
  {
    
    if(curr->val == x) {
      found = true;
    }
    curr = curr->next;
  }
  //@ close nodes(curr, nil);
  //@ close set(set, vals);
  return found;
}

void set_dispose(struct set* set)
  
//@ requires set(set, ?vals);
//@ ensures true;
{
  
  struct node* curr = set->head;
  //@ open set(set, vals);
  while(curr != 0) 
    //@ invariant nodes(curr, ?l);
  {
    struct node* nxt = curr->next;
    free(curr);
    curr = nxt;
  }
  
  free(set);
}

int main() 
  
//@ requires true;
//@ ensures true;
{
  struct set* set = create_set();
  if(set == 0) return 0;
  set_add(set, (void*) 1);
  set_add(set, (void*) 2);
  set_add(set, (void*) 3);
  bool cnt = set_contains(set, (void*) 1);
  assert(cnt);
  set_dispose(set);
  return 0;
}

/*@

fixpoint bool eq_voidptr(void* x, void* y) { return x == y; }

fixpoint bool existsb(bool (*p)(void*), list<void*> xs) {
  switch(xs) {
    case nil: return false;
    case cons(h, t): return p(h) || existsb(p, t);
  }
}

fixpoint list<T> take<T>(int n, list<T> xs) {
  switch(xs) {
    case nil: return nil;
    case cons(h, t): return n == 0 ? nil : cons(h, take(n - 1, t));
  }
}

fixpoint int length<T>(list<T> xs) {
  switch(xs) {
    case nil: return 0;
    case cons(h, t): return 1 + length(t);
  }
}

@*/