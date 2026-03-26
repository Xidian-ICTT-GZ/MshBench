#include "stdlib.h"

/*@ 
predicate nodes(struct node* n;);
predicate set(struct set* s; struct node* head) = s->head |-> head &*& malloc_block_set(s) &*& nodes(head);
predicate node(struct node* n; void* val, struct node* next) = n->val |-> val &*& n->next |-> next &*& malloc_block_node(n);
predicate nodes(struct node* n;) =
  n == 0 ?
    true
  :
    node(n, ?val, ?next) &*& nodes(next);
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
//@ ensures set(result, 0) &*& result != 0 || result == 0;
  
  
{
  struct set* set = malloc(sizeof(struct set));
  if(set == 0) return 0;
  set->head = 0;
  //@ close node(set, 0, 0); // Not needed; instead close set predicate
  //@ close set(set, 0);
  
  
  return set;
}

void set_add(struct set* set, void* x)
//@ requires set(set, ?old_head);
//@ ensures set(set, ?new_head) &*& new_head != 0;
  
  
{
  
  
  struct node* n = malloc(sizeof(struct node));
  if(n == 0) abort();
  //@ close node(n, x, old_head);
  n->next = set->head;
  n->val = x;
  set->head = n;
  //@ close set(set, n);
  
  
}

bool set_contains(struct set* set, void* x)
//@ requires set(set, ?head);
//@ ensures set(set, head) &*& result == (x != 0 ? mem(x, head) : false);

//@ requires set(set, ?head);
//@ ensures set(set, head);
  
  
{
  
  struct node* curr = set->head;
  bool found = false;
  //@ open set(set, head);
  //@ assert nodes(curr);
  //@ close set(set, curr);
  
  
  while(curr != 0 && ! found) 
  //@ invariant set(set, ?s_head) &*& nodes(curr) &*& s_head == curr || s_head != curr;
  //@ invariant found == false;
    
    
  {
    //@ open set(set, _);
    //@ open nodes(curr);
    //@ assert node(curr, ?val, ?next);
    
    if(curr->val == x) {
      
      found = true;
    }
    curr = curr->next;
    //@ if (!found) { close nodes(curr); close set(set, curr); }
    
    
    
    
  }
  //@ open set(set, _);
  //@ close set(set, head);
  
  
  return found;
}

void set_dispose(struct set* set)
//@ requires set(set, ?head);
//@ ensures true;
  
  
{
  //@ open set(set, head);
  //@ assert nodes(head);
  
  struct node* curr = set->head;
  while(curr != 0) 
  //@ invariant nodes(curr);
    
  {
    //@ open nodes(curr);
    //@ assert node(curr, ?val, ?next);
    
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
  //@ open set(set, 0);
  set_add(set, (void*) 1);
  set_add(set, (void*) 2);
  set_add(set, (void*) 3);
  bool cnt = set_contains(set, (void*) 1);
  //@ assert cnt == true;
  set_dispose(set);
  return 0;
}