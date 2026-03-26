#include <limits.h>
#include <stdbool.h>
#include <stdlib.h>

struct Node {
  struct Node* left;
  struct Node* right;
  struct Node* parent;
  int count;
};

/*@
predicate Node(struct Node* n) =
  n->left |-> ?left &*&
  n->right |-> ?right &*&
  n->parent |-> ?parent &*&
  n->count |-> ?count &*&
  malloc_block_Node(n);
@*/

struct Node* internalCreate(struct Node* parent)
  //@ requires true;
  //@ ensures Node(result);
{
  struct Node* n = malloc(sizeof(struct Node));
  if(n==0) {
    abort();
  } else {}
  n->left = 0;
  n->right = 0;
  n->parent = parent;
  n->count = 1;
  //@ close Node(n);
  return n;
}

struct Node* internalAddLeft(struct Node* node)
  //@ requires Node(node);
  //@ ensures Node(node) &*& Node(result);
{
    //@ open Node(node);
    struct Node* child = internalCreate(node);
    node->left = child;
    //@ close Node(node);
    fix(node);
    return child;
}

void fix(struct Node* node)
  //@ requires Node(node);
  //@ ensures Node(node);
{
  //@ open Node(node);
  int tmp = node->count;
  if (tmp == INT_MAX) {
    abort();
  }
  node->count = tmp + 1;
  struct Node* parent = node->parent;
  //@ close Node(node);
  if(parent==0){
  } else {
    //@ open Node(parent);
    //@ close Node(parent);
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
  //@ requires Node(n);
  //@ ensures Node(n);
{
  //@ open Node(n);
  int c = n->count;
  //@ close Node(n);
  return c;
}

struct Node* create()
  //@ requires true;
  //@ ensures Node(result);
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
  //@ close Node(n);
  return n;
}

struct Node* addLeft(struct Node* node)
  //@ requires Node(node);
  //@ ensures Node(node) &*& Node(result);
{
  struct Node* newChild = internalAddLeft(node);
  return newChild;
}

int getNbOfNodes(struct Node* n)
  //@ requires Node(n);
  //@ ensures Node(n);
{
    int c = internalGetNbOfNodes(n);
    return c;
}

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