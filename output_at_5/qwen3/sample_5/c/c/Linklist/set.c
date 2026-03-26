#include "stdlib.h"
#include <stdbool.h>

struct node {
  void* val;
  struct node* next;
};

struct set {
  struct node* head;
  
};

//@ predicate set(struct set* s) = s != 0 &*& s->head == 0;
//@ predicate list(struct node* n) = n == 0 |&*& n != 0 &*& n->next == 0 ? true : list(n->next);
//@ predicate set_list(struct set* s, struct node* head) = s != 0 &*& s->head == head &*& list(head);

struct set* create_set()
  
  
{
  struct set* set = malloc(sizeof(struct set));
  if(set == 0) return 0;
  set->head = 0;
  
  
  return set;
}

void set_add(struct set* set, void* x)
  
  
{
  //@ requires set_list(set, set->head);
  struct node* n = malloc(sizeof(struct node));
  if(n == 0) abort();
  n->next = set->head;
  n->val = x;
  set->head = n;
  //@ ensures set_list(set, set->head);
}

bool set_contains(struct set* set, void* x)
  
  
{
  //@ requires set_list(set, set->head);
  struct node* curr = set->head;
  bool found = false;
  
  while(curr != 0 && ! found) 
    {
      //@ invariant set_list(set, curr) &*& (found ? curr->val == x : true);
      if(curr->val == x) {
        found = true;
      }
      curr = curr->next;
    }
  //@ ensures found ? set_list(set, set->head) &*& exists struct node* p; p != 0 &*& p->val == x &*& p->next == 0 ? true : true : set_list(set, set->head);
  return found;
}

void set_dispose(struct set* set)
  
  
{
  //@ requires set_list(set, set->head);
  struct node* curr = set->head;
  while(curr != 0) 
  {
    struct node* nxt = curr->next;
    free(curr);
    curr = nxt;
  }
  free(set);
  //@ ensures true;
}

int main() 
  
  
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