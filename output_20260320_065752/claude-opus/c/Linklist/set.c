#include "stdlib.h"

/*@ 
predicate node(struct node* n; void* val, struct node* next) =
  n != 0 &*&
  n->val |-> val &*&
  n->next |-> next;
  
predicate nodes(struct node* n) =
  n == 0 ? emp : node(n, ?val, ?next) &*& nodes(next);

predicate set(struct set* s; struct node* head) =
  s != 0 &*&
  s->head |-> head &*&
  nodes(head);
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
  //@ ensures result == 0 ? true : set(result, 0);
{
  struct set* set = malloc(sizeof(struct set));
  if(set == 0) return 0;
  set->head = 0;
  
  //@ close set(set, 0);
  return set;
}

void set_add(struct set* set, void* x)
  //@ requires set(set, ?head);
  //@ ensures set(set, cons(?x1, head) || nodes added with val x);
{
  //@ open set(set, head);
  
  struct node* n = malloc(sizeof(struct node));
  if(n == 0) abort();
  n->next = set->head;
  n->val = x;
  set->head = n;
  
  //@ close node(n, x, head);
  //@ close set(set, n);
}

bool set_contains(struct set* set, void* x)
  //@ requires set(set, ?head);
  //@ ensures set(set, head) &*& result == (exists(struct node* curr; nodes(head) & curr->val == x));
{
  //@ open set(set, head);
  
  struct node* curr = set->head;
  bool found = false;
  //@ predicate loop_inv(struct node* curr0, bool found0) =
  //@     nodes(curr0) &*& found == found0;
  //@ open nodes(head);
  //@ close loop_inv(curr, found);
  
  while(curr != 0 && ! found) 
    //@ invariant loop_inv(curr, found);
  {
    //@ open loop_inv(curr, found);
    //@ open node(curr, ?val, ?next);
    if(curr->val == x) {
      found = true;
    }
    curr = curr->next;
    //@ close loop_inv(curr, found);
  }
  
  //@ close nodes(head);
  //@ close set(set, head);
  return found;
}

void set_dispose(struct set* set)
  //@ requires set(set, ?head);
  //@ ensures true;
{
  //@ open set(set, head);
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