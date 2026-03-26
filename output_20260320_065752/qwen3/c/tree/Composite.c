/*@ predicate tree(struct Node* n; int nb) =
    n == 0 ?
      nb == 0
    :
      malloc_block_Node(n) &*&
      tree(n->left, ?nbL) &*&
      tree(n->right, ?nbR) &*&
      nb == 1 + nbL + nbR;
@*/

/*@ predicate valid_tree(struct Node* root) =
    tree(root, ?nb) &*& root != 0;
@*/

//@ #include <stdlib.h>
//@ #include <limits.h>

struct Node {
  struct Node* left;
  struct Node* right;
  struct Node* parent;
  int count;
};

//@ requires true;
//@ ensures valid_tree(result);
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
  //@ close tree(n, 1);
  //@ close valid_tree(n);
  return n;
}

//@ requires valid_tree(node);
//@ ensures valid_tree(node) &*& valid_tree(result);
struct Node* addLeft(struct Node* node)
{
  struct Node* newChild = internalAddLeft(node);
  return newChild;
}

//@ requires valid_tree(n);
//@ ensures result == n->count;
int getNbOfNodes(struct Node* n)
{
  int c = internalGetNbOfNodes(n);
  return c;
}

//@ requires parent == 0 ? true : valid_tree(parent);
//@ ensures valid_tree(result);
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
  //@ close tree(n, 1);
  //@ close valid_tree(n);
  return n;
}

//@ requires valid_tree(node);
//@ ensures valid_tree(node) &*& valid_tree(result);
struct Node* internalAddLeft(struct Node* node)
{
  //@ open valid_tree(node);
  //@ open tree(node, ?nbOld);
  struct Node* child = internalCreate(node);
  node->left = child;
  fix(node);
  //@ close tree(node, ?nbNew);
  //@ close valid_tree(node);
  return child;
}

//@ requires valid_tree(node);
//@ ensures valid_tree(node);
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
    //@ open valid_tree(node);
    //@ open tree(node, _);
    //@ close tree(node, _);
    //@ close valid_tree(node);
    fix(parent);
  }
}

//@ requires true;
//@ ensures false;
void abort()
{
  while(true)
  {
  }
}

//@ requires valid_tree(n);
//@ ensures result == n->count;
int internalGetNbOfNodes(struct Node* n)
{
  int c = n->count;
  return c;
}

//@ requires true;
//@ ensures true;
int main() 
{
  struct Node* mytree = create();
  struct Node* child = addLeft(mytree);
  
  struct Node* child2 = addLeft(child);
  
  int c = getNbOfNodes(child2);
  //@ assert(c == 1);
  abort();
}