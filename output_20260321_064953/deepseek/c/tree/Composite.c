#include <limits.h>
#include <stdbool.h>
#include <stdlib.h>

struct Node;

/*@
predicate Node(struct Node *node; struct Node *left, struct Node *right, struct Node *parent, int count) =
    node->left |-> left &*&
    node->right |-> right &*&
    node->parent |-> parent &*&
    node->count |-> count &*&
    malloc_block_Node(node);
@*/

struct Node* create();
/*@ requires true;
    ensures Node(result, 0, 0, 0, 1);
@*/

struct Node* addLeft(struct Node* node);
/*@ requires Node(node, ?left, ?right, ?parent, ?count);
    ensures Node(node, ?newLeft, right, parent, count + 1) &*& Node(newLeft, 0, 0, node, 1);
@*/

int getNbOfNodes(struct Node* n);
/*@ requires Node(n, ?left, ?right, ?parent, ?count);
    ensures Node(n, left, right, parent, count) &*& result == count;
@*/

struct Node* internalCreate(struct Node* parent);
/*@ requires true;
    ensures Node(result, 0, 0, parent, 1);
@*/

struct Node* internalAddLeft(struct Node* node);
/*@ requires Node(node, ?left, ?right, ?parent, ?count);
    ensures Node(node, ?child, right, parent, count + 1) &*& Node(child, 0, 0, node, 1);
@*/

void fix(struct Node* node);
/*@ requires Node(node, ?left, ?right, ?parent, ?count);
    ensures Node(node, left, right, parent, count + 1);
@*/

int internalGetNbOfNodes(struct Node* n);
/*@ requires Node(n, ?left, ?right, ?parent, ?count);
    ensures Node(n, left, right, parent, count) &*& result == count;
@*/

int main() 
//@ requires true;
//@ ensures true;
{
  struct Node* mytree = create();
  struct Node* child = addLeft(mytree);
  //@ open Node(mytree, _, _, _, _);
  //@ close Node(mytree, _, _, _, _);
  
  struct Node* child2 = addLeft(child);
  //@ open Node(child, _, _, _, _);
  //@ close Node(child, _, _, _, _);
  
  int c = getNbOfNodes(child2);
  //@ assert c == 1;
  assert(c==1);
  abort();
  return 0;
}

struct Node* create() 
//@ requires true;
//@ ensures Node(result, 0, 0, 0, 1);
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
  //@ close Node(n, 0, 0, 0, 1);
  return n;
}

struct Node* addLeft(struct Node* node)
//@ requires Node(node, ?left, ?right, ?parent, ?count);
//@ ensures Node(node, ?newLeft, right, parent, count + 1) &*& Node(newLeft, 0, 0, node, 1);
{
  //@ open Node(node, left, right, parent, count);
  struct Node* newChild = internalAddLeft(node);
  //@ close Node(node, newChild, right, parent, count + 1);
  return newChild;
}

int getNbOfNodes(struct Node* n)
//@ requires Node(n, ?left, ?right, ?parent, ?count);
//@ ensures Node(n, left, right, parent, count) &*& result == count;
{
    //@ open Node(n, left, right, parent, count);
    int c = internalGetNbOfNodes(n);
    //@ close Node(n, left, right, parent, count);
    return c;
}

struct Node {
  struct Node* left;
  struct Node* right;
  struct Node* parent;
  int count;
};

struct Node* internalCreate(struct Node* parent)
//@ requires true;
//@ ensures Node(result, 0, 0, parent, 1);
{
  struct Node* n = malloc(sizeof(struct Node));
  if(n==0) {
    abort();
  } else {}
  n->left = 0;
  n->right = 0;
  n->parent = parent;
  n->count = 1;
  //@ close Node(n, 0, 0, parent, 1);
  return n;
}

struct Node* internalAddLeft(struct Node* node)
//@ requires Node(node, ?left, ?right, ?parent, ?count);
//@ ensures Node(node, ?child, right, parent, count + 1) &*& Node(child, 0, 0, node, 1);
{
    //@ open Node(node, left, right, parent, count);
    struct Node* child = internalCreate(node);
    node->left = child;
    fix(node);
    //@ close Node(node, child, right, parent, count + 1);
    return child;
}

void fix(struct Node* node)
//@ requires Node(node, ?left, ?right, ?parent, ?count);
//@ ensures Node(node, left, right, parent, count + 1);
{
  //@ open Node(node, left, right, parent, count);
  int tmp = node->count;
  if (tmp == INT_MAX) {
    abort();
  }
  node->count = tmp + 1;
  
  struct Node* parent = node->parent;
  if(parent==0){
    //@ close Node(node, left, right, parent, count + 1);
  } else {
    //@ close Node(node, left, right, parent, count + 1);
    fix(parent);
    //@ open Node(node, left, right, parent, count + 1);
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
//@ requires Node(n, ?left, ?right, ?parent, ?count);
//@ ensures Node(n, left, right, parent, count) &*& result == count;
{
  //@ open Node(n, left, right, parent, count);
  int c = n->count;
  //@ close Node(n, left, right, parent, count);
  return c;
}