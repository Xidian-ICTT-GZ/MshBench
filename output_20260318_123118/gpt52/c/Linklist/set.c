#include "stdlib.h"

/*@

predicate nodes(struct node *n; list<void*> vs) =
  n == 0 ?
    vs == nil
  :
    n->val |-> ?v &*& n->next |-> ?next &*& malloc_block_node(n) &*&
    nodes(next; ?vs0) &*& vs == cons(v, vs0);

predicate setp(struct set *s; list<void*> vs) =
  s->head |-> ?h &*& malloc_block_set(s) &*& nodes(h; vs);

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
  //@ ensures result == 0 ? true : setp(result; nil);
{
  struct set* set = malloc(sizeof(struct set));
  if(set == 0) return 0;
  set->head = 0;
  
  
  return set;
}

void set_add(struct set* set, void* x)
  //@ requires setp(set; ?vs);
  //@ ensures setp(set; cons(x, vs));
{
  
  
  struct node* n = malloc(sizeof(struct node));
  if(n == 0) abort();
  n->next = set->head;
  n->val = x;
  set->head = n;
  
  
}

bool set_contains(struct set* set, void* x)
  //@ requires setp(set; ?vs);
  //@ ensures setp(set; vs);
{
  
  struct node* curr = set->head;
  bool found = false;
  
  
  
  //@ assert nodes(curr; ?cvs);
  while(curr != 0 && ! found) 
    //@ invariant nodes(curr; ?vs1) &*& found == false;
  {
    
    
    if(curr->val == x) {
      
      found = true;
    }
    curr = curr->next;
    
    
    
    
  }
  
  
  //@ open nodes(curr; ?vs2);
  //@ close nodes(curr; vs2);
  //@ assert setp(set; vs);
  return found;
}

void set_dispose(struct set* set)
  //@ requires setp(set; ?vs);
  //@ ensures true;
{
  
  struct node* curr = set->head;
  //@ open setp(set; vs);
  while(curr != 0) 
    //@ invariant nodes(curr; ?vs1);
  {
    
    //@ open nodes(curr; vs1);
    struct node* nxt = curr->next;
    free(curr);
    curr = nxt;
  }
  //@ open nodes(curr; ?vs2);
  
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