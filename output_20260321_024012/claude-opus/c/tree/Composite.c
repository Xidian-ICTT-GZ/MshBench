/*@
predicate node(struct Node* n; struct Node* left, struct Node* right, struct Node* parent, int count) =
  n->left |-> left &*& n->right |-> right &*& n->parent |-> parent &*& n->count |-> count;
@*/

#include <limits.h>
#include <stdlib.h>
#include <stdbool.h>

struct Node {
  struct Node* left;
  struct Node* right;
  struct Node* parent;
  int count;
};

struct Node* internalCreate(struct Node* parent);
struct Node* internalAddLeft(struct Node* node);
void fix(struct Node* node);
int internalGetNbOfNodes(struct Node* n);
void abort();

int main() 
//@ requires true;
//@ ensures true;
{
  struct Node* mytree = create();
  struct Node* child = addLeft(mytree);
  
  struct Node* child2 = addLeft(child);
  
  int c = getNbOfNodes(child2);
  //@ assert c == 1;
  abort();
}

struct Node* create() 
//@ requires true;
//@ ensures node(result, 0, 0, 0, 1);
{
  struct Node* n = malloc(sizeof(struct Node));
  if(n == 0) {
    abort();
  } else {}
  n->parent = 0;
  n->left = 0;
  n->right = 0;
  n->count = 1;
  //@ close node(n, 0, 0, 0, 1);
  return n;
}

struct Node* addLeft(struct Node* node)
//@ requires node(node, ?l, ?r, ?p, ?c);
//@ ensures node(result, 0, 0, node, 1) &*& node(node, result, r, p, c+1);
{
  struct Node* newChild = internalAddLeft(node);
  return newChild;
}

int getNbOfNodes(struct Node* n)
//@ requires node(n, ?l, ?r, ?p, ?c);
//@ ensures node(n, l, r, p, c) &*& result == c;
{
  int c = internalGetNbOfNodes(n);
  return c;
}

struct Node* internalCreate(struct Node* parent)
//@ requires true;
//@ ensures node(result, 0, 0, parent, 1);
{
  struct Node* n = malloc(sizeof(struct Node));
  if(n == 0) {
    abort();
  } else {}
  n->left = 0;
  n->right = 0;
  n->parent = parent;
  n->count = 1;
  //@ close node(n, 0, 0, parent, 1);
  return n;
}

struct Node* internalAddLeft(struct Node* node)
//@ requires node(node, ?l, ?r, ?p, ?c);
//@ ensures node(result, 0, 0, node, 1) &*& node(node, result, r, p, c + 1);
{
  struct Node* child = internalCreate(node);
  node->left = child;
  //@ open node(node, l, r, p, c);
  //@ open node(child, 0, 0, node, 1);
  fix(node);
  //@ close node(node, child, r, p, c+1);
  //@ close node(child, 0, 0, node, 1);
  return child;
}

void fix(struct Node* node)
//@ requires node(node, ?l, ?r, ?p, ?c);
//@ ensures node(node, l, r, p, c + 1);
{
  int tmp = node->count;
  if(tmp == INT_MAX) {
    abort();
  }
  node->count = tmp + 1;
  //@ open node(node, l, r, p, c);
  //@ close node(node, l, r, p, c+1);
  
  struct Node* parent = node->parent;
  if(parent == 0) {
    //@ open node(node, l, r, p, c+1);
  } else {
    //@ open node(node, l, r, p, c+1);
    fix(parent);
    //@ close node(node, l, r, p, c+1);
  }
}

void abort()
//@ requires true;
//@ ensures false;
{
  while(true) {
  }
}

int internalGetNbOfNodes(struct Node* n)
//@ requires node(n, ?l, ?r, ?p, ?c);
//@ ensures node(n, l, r, p, c) &*& result == c;
{
  int c = n->count;
  return c;
}