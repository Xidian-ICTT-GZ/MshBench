#include "stdlib.h"

//@ predicate set(struct set* s) = s != 0 &*& s->head == 0;
//@ predicate node_list(struct node* n, struct set* s) = 
//@   n == 0 &*& s != 0 &*& s->head == n |&*& true
//@   &*& node_list(n->next, s);
//@ predicate set_with_nodes(struct set* s, struct node* head) = 
//@   s != 0 &*& s->head == head &*& node_list(head, s);

struct node {
  void* val;
  struct node* next;
};

struct set {
  struct node* head;
  
};

struct set* create_set()
  
  
{
  struct set* set = malloc(sizeof(struct set));
  if(set == 0) return 0;
  set->head = 0;
  
  
  //@ open set(set);
  return set;
}

void set_add(struct set* set, void* x)
  
  
{
  //@ requires set_with_nodes(set, set->head);
  struct node* n = malloc(sizeof(struct node));
  if(n == 0) abort();
  n->next = set->head;
  n->val = x;
  set->head = n;
  //@ close set_with_nodes(set, n);
}

bool set_contains(struct set* set, void* x)
  
  
{
  //@ requires set_with_nodes(set, set->head);
  struct node* curr = set->head;
  bool found = false;
  
  while(curr != 0 && ! found) 
    {
      //@ invariant set_with_nodes(set, curr) &*& (found ? curr->val == x : true);
      if(curr->val == x) {
        found = true;
      }
      curr = curr->next;
    }
  return found;
}

void set_dispose(struct set* set)
  
  
{
  //@ requires set_with_nodes(set, set->head);
  struct node* curr = set->head;
  while(curr != 0) 
  {
    struct node* nxt = curr->next;
    free(curr);
    curr = nxt;
  }
  free(set);
  //@ close set(set);
}

int main() 
  
  
{
  struct set* set = create_set();
  if(set == 0) return 0;
  //@ open set(set);
  set_add(set, (void*) 1);
  set_add(set, (void*) 2);
  set_add(set, (void*) 3);
  bool cnt = set_contains(set, (void*) 1);
  assert(cnt);
  set_dispose(set);
  return 0;
}