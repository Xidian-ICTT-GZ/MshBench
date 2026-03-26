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
  n == 0 ?
    emp
  :
    n->val |-> ?v &*& n->next |-> ?next &*& malloc_block_node(n) &*& nodes(next);

predicate setp(struct set* s) =
  s->head |-> ?h &*& malloc_block_set(s) &*& nodes(h);
@*/

struct set* create_set()
  //@ requires true;
  //@ ensures result == 0 ? true : setp(result);
  
  
{
  struct set* set = malloc(sizeof(struct set));
  if(set == 0) return 0;
  set->head = 0;
  //@ close nodes(0);
  //@ close setp(set);
  
  
  return set;
}

void set_add(struct set* set, void* x)
  //@ requires setp(set);
  //@ ensures setp(set);
  
  
{
  //@ open setp(set);
  
  
  struct node* n = malloc(sizeof(struct node));
  if(n == 0) abort();
  n->next = set->head;
  n->val = x;
  set->head = n;
  //@ close nodes(n);
  //@ close setp(set);
  
  
}

bool set_contains(struct set* set, void* x)
  //@ requires setp(set);
  //@ ensures setp(set);
  
  
{
  //@ open setp(set);
  
  struct node* curr = set->head;
  bool found = false;
  
  
  
  while(curr != 0 && ! found) 
    //@ invariant set->head |-> ?h &*& malloc_block_set(set) &*& nodes(h);
    
    
  {
    
    
    if(curr->val == x) {
      
      found = true;
    }
    curr = curr->next;
    
    
    
    
  }
  
  
  //@ close setp(set);
  return found;
}

void set_dispose(struct set* set)
  //@ requires setp(set);
  //@ ensures true;
  
  
{
  //@ open setp(set);
  
  struct node* curr = set->head;
  while(curr != 0) 
    //@ invariant nodes(curr);
    
  {
    //@ open nodes(curr);
    
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