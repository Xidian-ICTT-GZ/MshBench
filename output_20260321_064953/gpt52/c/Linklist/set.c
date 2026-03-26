#include "stdlib.h"

/*@
predicate nodes(struct node *n) =
  n == 0 ?
    true
  :
    n->val |-> ?v &*& n->next |-> ?next &*& malloc_block_node(n) &*& nodes(next);

predicate setp(struct set *s) =
  s == 0 ?
    true
  :
    s->head |-> ?h &*& malloc_block_set(s) &*& nodes(h);
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
  //@ ensures setp(result);
  
  
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
  //@ open nodes(?h);
  
  struct node* n = malloc(sizeof(struct node));
  if(n == 0) abort();
  n->next = set->head;
  n->val = x;
  //@ close nodes(n);
  set->head = n;
  //@ close setp(set);
  
  
}

bool set_contains(struct set* set, void* x)
  //@ requires setp(set);
  //@ ensures setp(set);
  
  
{
  //@ open setp(set);
  
  struct node* curr = set->head;
  bool found = false;
  
  //@ close nodes(0);
  //@ close nodes(curr);
  //@ open nodes(curr);
  
  while(curr != 0 && ! found) 
    //@ invariant nodes(curr) &*& set->head |-> ?h &*& malloc_block_set(set);
    
    
  {
    //@ open nodes(curr);
    
    
    if(curr->val == x) {
      
      found = true;
    }
    struct node* next = curr->next;
    //@ close nodes(curr);
    curr = next;
    
    
    
    
  }
  //@ close nodes(curr);
  //@ close setp(set);
  
  return found;
}

void set_dispose(struct set* set)
  //@ requires setp(set);
  //@ ensures true;
  
  
{
  //@ open setp(set);
  struct node* curr = set->head;
  //@ open nodes(curr);
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