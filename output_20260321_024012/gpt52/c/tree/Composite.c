#include <stdlib.h>
#include <limits.h>
#include <stdbool.h>

/*@

predicate node(struct Node* n; struct Node* left, struct Node* right, struct Node* parent, int count) =
  n->left |-> left &*& n->right |-> right &*& n->parent |-> parent &*& n->count |-> count;

@*/

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
  //@ ensures result != 0;
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
  
  
  
  return n;
}

struct Node* addLeft(struct Node* node)
  //@ requires true;
  //@ ensures true;
{
  
  
  
  
  
  
  
  
  

  
  

  struct Node* newChild = internalAddLeft(node);
  
  
  
  
  
  
  
  return newChild;
}

int getNbOfNodes(struct Node* n)
  //@ requires true;
  //@ ensures true;
{
    
    
    
    
    
    
    int c = internalGetNbOfNodes(n);
    
    
    
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
  //@ ensures result != 0;
{
  struct Node* n = malloc(sizeof(struct Node));
  if(n==0) {
    abort();
  } else {}
  n->left = 0;
  n->right = 0;
  n->parent = parent;
  n->count = 1;
  
  return n;
}

struct Node* internalAddLeft(struct Node* node)
  //@ requires true;
  //@ ensures true;

  

{
    struct Node* child = internalCreate(node);
    node->left = child;
    fix(node);
    return child;
}

void fix(struct Node* node)
  //@ requires true;
  //@ ensures true;
     
  
{
  int tmp = node->count;
  if (tmp == INT_MAX) {
    abort();
  }
  node->count = tmp + 1;
  
  struct Node* parent = node->parent;
  if(parent==0){
  } else {
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
  //@ requires true;
  //@ ensures true;
  
  
{
  
  int c = n->count;
  
  return c;
}