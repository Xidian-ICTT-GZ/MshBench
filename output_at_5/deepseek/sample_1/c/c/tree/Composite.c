#include <limits.h>
#include <stdbool.h>
#include <stdlib.h>

/*@
predicate Node(struct Node* n; struct Node* left, struct Node* right, struct Node* parent, int count) =
  n->left |-> left &*&
  n->right |-> right &*&
  n->parent |-> parent &*&
  n->count |-> count &*&
  malloc_block_Node(n);
@*/

struct Node {
  struct Node* left;
  struct Node* right;
  struct Node* parent;
  int count;
};

//@ predicate_family OWN(void* p);

struct Node* internalCreate(struct Node* parent)
  //@ requires true;
  //@ ensures OWN(result);
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
  //@ close OWN(n);
  return n;
}

struct Node* internalAddLeft(struct Node* node)
  //@ requires OWN(node);
  //@ ensures OWN(node) &*& OWN(result);
{
    //@ open OWN(node);
    struct Node* child = internalCreate(node);
    node->left = child;
    //@ close Node(node, child, node->right, node->parent, node->count);
    fix(node);
    //@ close OWN(node);
    return child;
}

void fix(struct Node* node)
  //@ requires OWN(node);
  //@ ensures OWN(node);
{
  //@ open OWN(node);
  int tmp = node->count;
  if (tmp == INT_MAX) {
    abort();
  }
  node->count = tmp + 1;
  //@ close Node(node, node->left, node->right, node->parent, node->count);
  
  struct Node* parent = node->parent;
  if(parent==0){
    //@ close OWN(node);
  } else {
    //@ close OWN(node);
    fix(parent);
    //@ open OWN(node);
    //@ close OWN(node);
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
  //@ requires OWN(n);
  //@ ensures OWN(n);
{
  //@ open OWN(n);
  int c = n->count;
  //@ close OWN(n);
  return c;
}

struct Node* create()
  //@ requires true;
  //@ ensures OWN(result);
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
  //@ close OWN(n);
  return n;
}

struct Node* addLeft(struct Node* node)
  //@ requires OWN(node);
  //@ ensures OWN(node) &*& OWN(result);
{
  struct Node* newChild = internalAddLeft(node);
  return newChild;
}

int getNbOfNodes(struct Node* n)
  //@ requires OWN(n);
  //@ ensures OWN(n);
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