/*@ predicate tree(struct Node* n; struct Node* parent, int count) =
  n == 0 ?
    count == 0
  :
    malloc_block_Node(n) &*&
    n->left |-> ?l &*& n->right |-> ?r &*& n->parent |-> parent &*& n->count |-> count &*&
    1 <= count &*&
    tree(l, n, ?cl) &*& tree(r, n, ?cr) &*& count == 1 + cl + cr;
@*/

//@ #include <stdlib.h>
//@ #include <limits.h>

struct Node {
  struct Node* left;
  struct Node* right;
  struct Node* parent;
  int count;
};

/*@ predicate valid_tree(struct Node* root) =
  tree(root, 0, ?c);
@*/

struct Node* internalCreate(struct Node* parent)
//@ requires parent != 0 ? tree(parent, ?pparent, ?pc) : true;
//@ ensures parent != 0 ? tree(parent, pparent, pc) &*& tree(result, parent, 1) : tree(result, parent, 1);
{
  struct Node* n = malloc(sizeof(struct Node));
  if(n==0) {
    abort();
  } else {}
  n->left = 0;
  n->right = 0;
  n->parent = parent;
  n->count = 1;
  
  //@ close tree(n, parent, 1);
  return n;
}

struct Node* internalAddLeft(struct Node* node)
//@ requires tree(node, ?parent, ?old_count) &*& old_count < INT_MAX;
//@ ensures tree(node, parent, ?new_count) &*& new_count == old_count + 1 &*& tree(result, node, 1);
{
    struct Node* child = internalCreate(node);
    //@ open tree(node, parent, old_count);
    node->left = child;
    //@ assert tree(child, node, 1);
    fix(node);
    //@ open tree(node, _, _); // reopened by fix
    return child;
}

void fix(struct Node* node)
//@ requires tree(node, ?parent, ?old_count) &*& old_count < INT_MAX;
//@ ensures tree(node, parent, old_count + 1);
{
  int tmp = node->count;
  if (tmp == INT_MAX) {
    abort();
  }
  node->count = tmp + 1;
  
  struct Node* parent = node->parent;
  if(parent==0){
    //@ close tree(node, parent, tmp + 1);
  } else {
    //@ open tree(node, parent, tmp);
    //@ assert tree(node->left, node, ?cl) &*& tree(node->right, node, ?cr);
    //@ close tree(node, parent, tmp + 1);
    fix(parent);
  }
}

int internalGetNbOfNodes(struct Node* n)
//@ requires tree(n, ?parent, ?c);
//@ ensures tree(n, parent, c) &*& result == c;
{
  
  int c = n->count;
  
  return c;
}

struct Node* create() 
//@ requires true;
//@ ensures valid_tree(result);
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
  
  //@ close tree(n, 0, 1);
  //@ close valid_tree(n);
  return n;
}

struct Node* addLeft(struct Node* node)
//@ requires valid_tree(node) &*& internalGetNbOfNodes(node) < INT_MAX;
//@ ensures valid_tree(node) &*& valid_tree(result);
{
  struct Node* newChild = internalAddLeft(node);
  return newChild;
}

int getNbOfNodes(struct Node* n)
//@ requires valid_tree(n);
//@ ensures valid_tree(n) &*& result == internalGetNbOfNodes(n);
{
  int c = internalGetNbOfNodes(n);
  return c;
}

void abort()
//@ requires true;
//@ ensures false;
{
  while(true)
  {
  }
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