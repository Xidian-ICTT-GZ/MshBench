#include "stdlib.h"

/*@
predicate nodes(struct node* n) =
  n == 0 ?
    emp
  :
    malloc_block_node(n) &*& nodes(n->next);
@*/

/*@
predicate set_predicate(struct set* s) =
  malloc_block_set(s) &*& nodes(s->head);
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
  //@ ensures set_predicate(result) || result == 0;
{
  struct set* set = malloc(sizeof(struct set));
  if(set == 0) return 0;
  set->head = 0;
  //@ close nodes(0);
  //@ close set_predicate(set);
  return set;
}

void set_add(struct set* set, void* x)
  //@ requires set_predicate(set);
  //@ ensures set_predicate(set);
{
  //@ open set_predicate(set);
  struct node* n = malloc(sizeof(struct node));
  if(n == 0) abort();
  n->next = set->head;
  n->val = x;
  set->head = n;
  //@ close nodes(n);
  //@ close set_predicate(set);
}

bool set_contains(struct set* set, void* x)
  //@ requires set_predicate(set);
  //@ ensures set_predicate(set);
{
  //@ open set_predicate(set);
  struct node* curr = set->head;
  bool found = false;
  //@ while(curr != 0 && !found)
    //@ invariant nodes(curr) &*& set->head |-> ?h &*& nodes(h);
  while(curr != 0 && !found)
  {
    //@ open nodes(curr);
    if(curr->val == x) {
      found = true;
      //@ close nodes(curr);
    } else {
      struct node* next = curr->next;
      //@ close nodes(curr);
      curr = next;
    }
  }
  //@ close set_predicate(set);
  return found;
}

void set_dispose(struct set* set)
  //@ requires set_predicate(set);
  //@ ensures true;
{
  //@ open set_predicate(set);
  struct node* curr = set->head;
  //@ while(curr != 0)
    //@ invariant nodes(curr);
  while(curr != 0)
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