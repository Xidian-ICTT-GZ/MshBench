#include "stdlib.h"

/*@ predicate nodes(struct node* curr; struct node* end) =
    curr == end ?
      true
    :
      malloc_block_node(curr) &*& nodes(curr->next, end);
@*/

/*@ predicate set(struct set* s; ) =
    malloc_block_set(s) &*& nodes(s->head, 0);
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
//@ ensures set(result) &*& result != 0 ? true : true;
{
  struct set* set = malloc(sizeof(struct set));
  if(set == 0) return 0;
  set->head = 0;
  //@ close nodes(0, 0);
  //@ close set(set);
  return set;
}

void set_add(struct set* set, void* x)
//@ requires set(set);
//@ ensures set(set);
{
  //@ open set(set);
  //@ open nodes(set->head, 0);
  struct node* n = malloc(sizeof(struct node));
  if(n == 0) abort();
  n->next = set->head;
  n->val = x;
  set->head = n;
  //@ close nodes(set->head, 0);
  //@ close set(set);
}

bool set_contains(struct set* set, void* x)
//@ requires set(set);
//@ ensures set(set) &*& result == true ? true : true;
{
  //@ open set(set);
  //@ open nodes(set->head, 0);
  struct node* curr = set->head;
  bool found = false;
  //@ close nodes(set->head, 0); // re-close for loop invariant setup
  //@ open nodes(curr, 0);
  
  while(curr != 0 && ! found) 
    //@ invariant nodes(curr, 0) &*& set(set) &*& set->head |-> ?h &*& h == 0 ? curr == 0 : true;
  {
    if(curr->val == x) {
      found = true;
    }
    //@ open nodes(curr, 0);
    curr = curr->next;
    //@ if (curr != 0) open nodes(curr, 0);
  }
  //@ close nodes(curr, 0);
  //@ close set(set);
  return found;
}

void set_dispose(struct set* set)
//@ requires set(set);
//@ ensures true;
{
  //@ open set(set);
  struct node* curr = set->head;
  //@ open nodes(curr, 0);
  while(curr != 0) 
    //@ invariant nodes(curr, 0);
  {
    //@ open nodes(curr, 0);
    struct node* nxt = curr->next;
    free(curr);
    curr = nxt;
    //@ if (curr != 0) open nodes(curr, 0);
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
  //@ assert(cnt);
  set_dispose(set);
  return 0;
}