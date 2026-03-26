#include "stdlib.h"
#include "assert.h"

/*@ predicate set(struct set* s; list<void*> values) =
  s != 0 &*&
  malloc_block_set(s) &*&
  nodes(s->head, values);
@*/

/*@ predicate nodes(struct node* n; list<void*> values) =
  n == 0 ?
    values == nil
  :
    malloc_block_node(n) &*&
    n->val |-> ?v &*&
    n->next |-> ?next &*&
    nodes(next, ?rest) &*&
    values == cons(v, rest);
@*/

struct node {
  void* val;
  struct node* next;
};

struct set {
  struct node* head;
  
};

struct set* create_set()
//@ requires true;
//@ ensures set(result, nil) || result == 0;
{
  struct set* set = malloc(sizeof(struct set));
  if(set == 0) return 0;
  set->head = 0;
  //@ close nodes(0, nil);
  //@ close set(set, nil);
  return set;
}

void set_add(struct set* set, void* x)
//@ requires set(set, ?old_values);
//@ ensures set(set, cons(x, old_values));
{
  //@ open set(set, old_values);
  //@ open nodes(set->head, old_values);
  struct node* n = malloc(sizeof(struct node));
  if(n == 0) abort();
  n->next = set->head;
  n->val = x;
  set->head = n;
  //@ close nodes(n, cons(x, old_values));
  //@ close set(set, cons(x, old_values));
}

bool set_contains(struct set* set, void* x)
//@ requires set(set, ?values);
//@ ensures set(set, values) &*& result == mem(x, values);
{
  //@ open set(set, values);
  //@ assert nodes(set->head, values);
  struct node* curr = set->head;
  bool found = false;
  //@ list<void*> curr_values = values;
  //@ invariant nodes(curr, curr_values) &*& set->head |-> ?h &*& h == set->head &*& mem(x, values) == (found || mem(x, curr_values));
  while(curr != 0 && ! found) 
  {
    //@ open nodes(curr, curr_values);
    //@ assert curr_values == cons(?v, ?rest);
    if(curr->val == x) {
      found = true;
      //@ curr_values = rest;
    }
    curr = curr->next;
    //@ if (!found) curr_values = rest;
    //@ if (found) close nodes(0, nil); // dummy to satisfy invariant syntax; actually not needed but safe
    //@ if (!found) close nodes(curr, curr_values);
  }
  //@ close nodes(curr, curr_values);
  //@ close set(set, values);
  return found;
}

void set_dispose(struct set* set)
//@ requires set(set, ?values);
//@ ensures true;
{
  //@ open set(set, values);
  struct node* curr = set->head;
  //@ open nodes(curr, values);
  while(curr != 0) 
  {
    struct node* nxt = curr->next;
    free(curr);
    curr = nxt;
    //@ open nodes(curr, _);
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
  //@ assert cnt == true;
  set_dispose(set);
  return 0;
}