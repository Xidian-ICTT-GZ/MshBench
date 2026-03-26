#include "stdlib.h"

/*@
predicate nodes(struct node* n; list<void*> vs) =
  n == 0 ?
    vs == nil
  :
    n->val |-> ?v &*& n->next |-> ?next &*& malloc_block_node(n) &*& nodes(next, ?vs0) &*& vs == cons(v, vs0);
  
predicate set(struct set* s; list<void*> vs) =
  s->head |-> ?head &*& malloc_block_set(s) &*& nodes(head, vs);
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
//@ ensures set(result, nil) |-> true;
  
  
{
  struct set* set = malloc(sizeof(struct set));
  if(set == 0) return 0;
  set->head = 0;
  //@ close nodes(0, nil);
  //@ close set(set, nil);
  
  
  return set;
}

void set_add(struct set* set, void* x)
//@ requires set(set, ?vs);
//@ ensures set(set, cons(x, vs));
  
  
{
  
  
  struct node* n = malloc(sizeof(struct node));
  if(n == 0) abort();
  //@ open set(set, vs);
  n->next = set->head;
  n->val = x;
  set->head = n;
  //@ close nodes(n, cons(x, vs));
  //@ close set(set, cons(x, vs));
  
  
}

bool set_contains(struct set* set, void* x)
//@ requires set(set, ?vs);
//@ ensures set(set, vs) &*& result == mem(x, vs);
  
  
{
  //@ open set(set, vs);
  //@ assert set->head |-> ?head &*& nodes(head, vs);
  struct node* curr = set->head;
  bool found = false;
  //@ int i = 0;
  //@ list<void*> curr_vs = vs;
  
  
  
  while(curr != 0 && ! found) 
  //@ invariant curr == 0 ? curr_vs == nil : nodes(curr, curr_vs) &*& mem(x, vs) == mem(x, curr_vs) &*& set->head |-> ?h &*& h == 0 ? vs == nil : true;
  //@ decreases length(curr_vs);
    
    
  {
    //@ open nodes(curr, curr_vs);
    //@ curr_vs = tail(curr_vs);
    
    if(curr->val == x) {
      
      found = true;
    }
    curr = curr->next;
    //@ if (!found) { close nodes(curr, curr_vs); }
    
    
    
    
  }
  //@ if (curr == 0) { close nodes(0, nil); }
  //@ close set(set, vs);
  
  
  return found;
}

void set_dispose(struct set* set)
//@ requires set(set, ?vs);
//@ ensures true;
  
  
{
  //@ open set(set, vs);
  struct node* curr = set->head;
  while(curr != 0) 
  //@ invariant nodes(curr, ?vs0);
  //@ decreases length(vs0);
    
  {
    //@ open nodes(curr, vs0);
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
  //@ assert cnt == true;
  set_dispose(set);
  return 0;
}