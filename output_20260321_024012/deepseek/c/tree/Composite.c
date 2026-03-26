#include <limits.h>
#include <stdlib.h>
#include <stdbool.h>

struct Node {
  struct Node* left;
  struct Node* right;
  struct Node* parent;
  int count;
};

/*@
predicate Node(struct Node* n; struct Node* left, struct Node* right, struct Node* parent, int count) =
  n->left |-> left &*&
  n->right |-> right &*&
  n->parent |-> parent &*&
  n->count |-> count &*&
  malloc_block_Node(n);
@*/

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
  //@ ensures Node(node, result, right, parent, count+1) &*& Node(result, 0, 0, node, 1);
{
    struct Node* child = internalCreate(node);
    //@ open Node(node, left, right, parent, count);
    node->left = child;
    //@ close Node(node, child, right, parent, count);
    fix(node);
    return child;
}

void fix(struct Node* node)
  //@ requires Node(node, ?left, ?right, ?parent, ?count);
  //@ ensures Node(node, left, right, parent, count+1);
{
  //@ open Node(node, left, right, parent, count);
  int tmp = node->count;
  if (tmp == INT_MAX) {
    abort();
  }
  node->count = tmp + 1;
  //@ close Node(node, left, right, parent, count+1);
  
  struct Node* parent = node->parent;
  if(parent==0){
  } else {
    //@ open Node(node, left, right, parent, count+1);
    fix(parent);
    //@ close Node(node, left, right, parent, count+1);
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
  //@ ensures Node(node, result, right, parent, count+1) &*& Node(result, 0, 0, node, 1);
{
  struct Node* newChild = internalAddLeft(node);
  return newChild;
}

int getNbOfNodes(struct Node* n)
  //@ requires Node(n, ?left, ?right, ?parent, ?count);
  //@ ensures Node(n, left, right, parent, count) &*& result == count;
{
    int c = internalGetNbOfNodes(n);
    return c;
}

int main()
  //@ requires true;
  //@ ensures false;
{
  struct Node* mytree = create();
  struct Node* child = addLeft(mytree);
  
  struct Node* child2 = addLeft(child);
  
  int c = getNbOfNodes(child2);
  //@ assert c == 1;
  abort();
}