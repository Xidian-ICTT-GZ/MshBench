#include "stdlib.h"

struct node {
  void* val;
  struct node* next;
};

struct set {
  struct node* head;
  
};

/*@
predicate nodes(struct node* n) =
  n == 0 ? true : malloc_block_node(n) &*& n->val |-> _ &*& n->next |-> ?next &*& nodes(next);
@*/

/*@
predicate set(struct set* s) =
  malloc_block_set(s) &*& s->head |-> ?head &*& nodes(head);
@*/

struct set* create_set()
  //@ requires true;
  //@ ensures result == 0 ? true : set(result);
  
{
  struct set* set = malloc(sizeof(struct set));
  if(set == 0) return 0;
  set->head = 0;
  //@ close nodes(0);
  //@ close set(set);
  return set;
}

void set_add(struct set* set, void* x)
  //@ requires set(set);
  //@ ensures set(set);
  
{
  //@ open set(set);
  struct node* n = malloc(sizeof(struct node));
  if(n == 0) abort();
  n->next = set->head;
  n->val = x;
  set->head = n;
  //@ close nodes(n);
  //@ close set(set);
}

bool set_contains(struct set* set, void* x)
  //@ requires set(set);
  //@ ensures set(set);
  
{
  //@ open set(set);
  struct node* curr = set->head;
  bool found = false;
  //@ struct node* prev = 0;
  //@ close nodes(curr);
  
  while(curr != 0 && ! found) 
    //@ invariant nodes(curr);
    
  {
    //@ open nodes(curr);
    
    if(curr->val == x) {
      
      found = true;
    }
    curr = curr->next;
    //@ close nodes(curr);
    
    
    
  }
  //@ close set(set);
  return found;
}

void set_dispose(struct set* set)
  //@ requires set(set);
  //@ ensures true;
  
{
  //@ open set(set);
  struct node* curr = set->head;
  while(curr != 0) 
    //@ invariant nodes(curr);
    
  {
    //@ open nodes(curr);
    struct node* nxt = curr->next;
    free(curr);
    curr = nxt;
  }
  //@ close nodes(0);
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