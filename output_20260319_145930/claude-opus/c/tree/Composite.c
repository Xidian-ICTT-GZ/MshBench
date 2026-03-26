#include <limits.h>
#include <stdlib.h>

struct Node {
  struct Node* left;
  struct Node* right;
  struct Node* parent;
  int count;
};

/*@
predicate node(struct Node* n; struct Node* left, struct Node* right, struct Node* parent, int count) =
  n->left |-> left &*& n->right |-> right &*& n->parent |-> parent &*& n->count |-> count;

predicate tree(struct Node* n;) =
  n == 0 ? true :
  node(n, ?left, ?right, ?parent, ?count) &*& tree(left) &*& tree(right) &*& count >= 1;

predicate subtree(struct Node* n, struct Node* root;) =
  n == root ? true :
  node(n, ?left, ?right, ?parent, ?count) &*& tree(left) &*& tree(right) &*& count >= 1 &*& parent != 0 &*& subtree(parent, root);
@*/

void abort()
  //@ requires true;
  //@ ensures false;
{
  while(true)
    //@ invariant true;
  {
  }
}

struct Node* internalCreate(struct Node* parent)
  //@ requires true;
  //@ ensures node(result, 0, 0, parent, 1);
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

void fix(struct Node* node)
  //@ requires node(node, ?left, ?right, ?parent, ?count) &*& count < INT_MAX &*& (parent == 0 ? true : subtree(parent, ?root));
  //@ ensures node(node, left, right, parent, count + 1) &*& (parent == 0 ? true : subtree(parent, root));
{
  int tmp = node->count;
  if (tmp == INT_MAX) {
    abort();
  }
  node->count = tmp + 1;
  
  struct Node* parent = node->parent;
  if(parent==0){
  } else {
    //@ open subtree(parent, _);
    fix(parent);
    //@ close subtree(parent, _);
  }
  
}

struct Node* internalAddLeft(struct Node* node)
  //@ requires node(node, 0, ?right, ?parent, ?count) &*& count < INT_MAX &*& (parent == 0 ? true : subtree(parent, ?root));
  //@ ensures node(node, result, right, parent, count + 1) &*& node(result, 0, 0, node, 1) &*& (parent == 0 ? true : subtree(parent, root));
{
    struct Node* child = internalCreate(node);
    node->left = child;
    fix(node);
    return child;
}

int internalGetNbOfNodes(struct Node* n)
  //@ requires node(n, ?left, ?right, ?parent, ?count);
  //@ ensures node(n, left, right, parent, count) &*& result == count;
{
  
  int c = n->count;
  
  return c;
}

struct Node* create() 
  //@ requires true;
  //@ ensures node(result, 0, 0, 0, 1);
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
  //@ requires node(node, 0, ?right, ?parent, ?count) &*& count < INT_MAX &*& (parent == 0 ? true : subtree(parent, ?root));
  //@ ensures node(node, result, right, parent, count + 1) &*& node(result, 0, 0, node, 1) &*& (parent == 0 ? true : subtree(parent, root));
{
  struct Node* newChild = internalAddLeft(node);
  
  return newChild;
}

int getNbOfNodes(struct Node* n)
  //@ requires node(n, ?left, ?right, ?parent, ?count);
  //@ ensures node(n, left, right, parent, count) &*& result == count;
{
    int c = internalGetNbOfNodes(n);
    
    return c;
}

int main() 
  //@ requires true;
  //@ ensures false;
{
  struct Node* mytree = create();
  //@ close subtree(mytree, mytree);
  struct Node* child = addLeft(mytree);
  //@ open subtree(mytree, mytree);
  //@ close subtree(mytree, mytree);
  //@ close subtree(child, mytree);
  struct Node* child2 = addLeft(child);
  //@ open subtree(child, mytree);
  //@ open subtree(mytree, mytree);
  
  int c = getNbOfNodes(child2);
  assert(c==1);
  abort();
}