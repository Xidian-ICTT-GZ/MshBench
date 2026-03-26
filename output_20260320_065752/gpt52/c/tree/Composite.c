#include <stdlib.h>
#include <limits.h>
#include <stdbool.h>

/*@

predicate node(struct Node* n; struct Node* left, struct Node* right, struct Node* parent, int count) =
  n->left |-> left &*& n->right |-> right &*& n->parent |-> parent &*& n->count |-> count;

predicate tree(struct Node* n; struct Node* parent) =
  n == 0 ?
    true
  :
    node(n, ?l, ?r, parent, ?c) &*& tree(l, n) &*& tree(r, n);

@*/

struct Node {
  struct Node* left;
  struct Node* right;
  struct Node* parent;
  int count;
};

struct Node* create();
struct Node* addLeft(struct Node* node);
int getNbOfNodes(struct Node* n);

struct Node* internalCreate(struct Node* parent);
struct Node* internalAddLeft(struct Node* node);
void fix(struct Node* node);
void abort();
int internalGetNbOfNodes(struct Node* n);

int main() 
//@ requires true;
//@ ensures true;
{
  struct Node* mytree = create();
  struct Node* child = addLeft(mytree);
  
  struct Node* child2 = addLeft(child);
  
  int c = getNbOfNodes(child2);
  assert(c==1);
  abort();
}

struct Node* create() 
//@ requires true;
//@ ensures tree(result, 0);
{
  struct Node* n = malloc(sizeof(struct Node));
  if(n==0){
    abort();
  } else {
  }
  n->parent = 0;
  n->left = 0;
  n->right = 0;
  n->count = 1;
  
  //@ close node(n, 0, 0, 0, 1);
  //@ close tree(0, n);
  //@ close tree(0, n);
  //@ close tree(n, 0);
  return n;
}

struct Node* addLeft(struct Node* node)
//@ requires tree(node, ?p);
//@ ensures tree(node, p) &*& tree(result, node);
{
  struct Node* newChild = internalAddLeft(node);
  return newChild;
}

int getNbOfNodes(struct Node* n)
//@ requires tree(n, ?p);
//@ ensures tree(n, p) &*& result >= 0;
{
    int c = internalGetNbOfNodes(n);
    return c;
}

struct Node* internalCreate(struct Node* parent)
//@ requires true;
//@ ensures tree(result, parent);
{
  struct Node* n = malloc(sizeof(struct Node));
  if(n==0) {
    abort();
  } else {}
  n->left = 0;
  n->right = 0;
  n->parent = parent;
  n->count = 1;
  //@ close node(n, 0, 0, parent, 1);
  //@ close tree(0, n);
  //@ close tree(0, n);
  //@ close tree(n, parent);
  return n;
}

struct Node* internalAddLeft(struct Node* node)
//@ requires tree(node, ?p) &*& node != 0;
//@ ensures tree(node, p) &*& tree(result, node);
{
    //@ open tree(node, p);
    //@ open node(node, ?oldLeft, ?oldRight, p, ?c0);
    struct Node* child = internalCreate(node);
    node->left = child;
    //@ close node(node, child, oldRight, p, c0);
    fix(node);
    //@ close tree(node, p);
    return child;
}

void fix(struct Node* node)
//@ requires tree(node, ?p) &*& node != 0;
//@ ensures tree(node, p);
{
  //@ open tree(node, p);
  //@ open node(node, ?l, ?r, p, ?c);
  int tmp = node->count;
  if (tmp == INT_MAX) {
    abort();
  }
  node->count = tmp + 1;
  
  struct Node* parent = node->parent;
  if(parent==0){
    //@ close node(node, l, r, p, tmp + 1);
    //@ close tree(l, node);
    //@ close tree(r, node);
    //@ close tree(node, p);
  } else {
    //@ close node(node, l, r, p, tmp + 1);
    //@ close tree(l, node);
    //@ close tree(r, node);
    //@ close tree(node, p);
    fix(parent);
  }
}

void abort()
//@ requires true;
//@ ensures false;
{
  while(true)
  //@ invariant true;
  {
  }
}

int internalGetNbOfNodes(struct Node* n)
//@ requires tree(n, ?p) &*& n != 0;
//@ ensures tree(n, p) &*& result == 1;
{
  //@ open tree(n, p);
  //@ open node(n, ?l, ?r, p, ?c);
  int c = n->count;
  //@ close node(n, l, r, p, c);
  //@ close tree(l, n);
  //@ close tree(r, n);
  //@ close tree(n, p);
  return c;
}