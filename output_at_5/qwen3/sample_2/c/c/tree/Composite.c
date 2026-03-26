#include <stdlib.h>
#include <limits.h>

typedef struct Node Node;

struct Node {
  struct Node* left;
  struct Node* right;
  struct Node* parent;
  int count;
};

/*@
predicate tree(Node* n, int count) =
  n != NULL &*&
  n->count == count &*&
  (n->left == NULL ? true : tree(n->left, n->left->count)) &*&
  (n->right == NULL ? true : tree(n->right, n->right->count)) &*&
  (n->parent == NULL ? true : true);
@*/

int main() 
{
  //@ requires true;
  struct Node* mytree = create();
  
  struct Node* child = addLeft(mytree);
  
  struct Node* child2 = addLeft(child);
  
  int c = getNbOfNodes(child2);
  assert(c==1);
  abort();
}

struct Node* create() 
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
{
  struct Node* newChild = internalAddLeft(node);
  return newChild;
}

int getNbOfNodes(struct Node* n)
{
  int c = internalGetNbOfNodes(n);
  return c;
}

struct Node* internalCreate(struct Node* parent)
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
{
    struct Node* child = internalCreate(node);
    node->left = child;
    fix(node);
    return child;
}

void fix(struct Node* node)
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
{
  while(true)
  {
  }
}

int internalGetNbOfNodes(struct Node* n)
{
  int c = n->count;
  return c;
}