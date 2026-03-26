/*@
predicate Node(struct Node* n; struct Node* parent, struct Node* left, struct Node* right, int count) =
    n->left |-> left &*& n->right |-> right &*& n->parent |-> parent &*& n->count |-> count &*& malloc_block_Node(n);
@*/

int main() 
//@ requires true;
//@ ensures true;
{
  struct Node* mytree = create();
  //@ open Node(mytree, _, _, _, _);
  struct Node* child = addLeft(mytree);
  //@ open Node(child, _, _, _, _);
  
  struct Node* child2 = addLeft(child);
  //@ open Node(child2, _, _, _, _);
  
  int c = getNbOfNodes(child2);
  //@ assert c == 1;
  assert(c==1);
  abort();
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
//@ requires Node(node, ?parent, ?left, ?right, ?count);
//@ ensures Node(node, parent, ?newLeft, right, count + 1) &*& Node(result, node, 0, 0, 1);
{
  //@ open Node(node, parent, left, right, count);
  struct Node* newChild = internalAddLeft(node);
  //@ close Node(node, parent, newChild, right, count + 1);
  return newChild;
}

int getNbOfNodes(struct Node* n)
//@ requires Node(n, ?parent, ?left, ?right, ?count);
//@ ensures Node(n, parent, left, right, count) &*& result == count;
{
    //@ open Node(n, parent, left, right, count);
    int c = internalGetNbOfNodes(n);
    //@ close Node(n, parent, left, right, count);
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
//@ ensures Node(result, parent, 0, 0, 1);
{
  struct Node* n = malloc(sizeof(struct Node));
  if(n==0) {
    abort();
  } else {}
  n->left = 0;
  n->right = 0;
  n->parent = parent;
  n->count = 1;
  //@ close Node(n, parent, 0, 0, 1);
  return n;
}

struct Node* internalAddLeft(struct Node* node)
//@ requires Node(node, ?parent, ?left, ?right, ?count);
//@ ensures Node(node, parent, result, right, count + 1) &*& Node(result, node, 0, 0, 1);
{
    //@ open Node(node, parent, left, right, count);
    struct Node* child = internalCreate(node);
    node->left = child;
    fix(node);
    //@ close Node(node, parent, child, right, count + 1);
    return child;
}

void fix(struct Node* node)
//@ requires Node(node, ?parent, ?left, ?right, ?count);
//@ ensures Node(node, parent, left, right, count + 1);
{
  //@ open Node(node, parent, left, right, count);
  int tmp = node->count;
  if (tmp == INT_MAX) {
    abort();
  }
  node->count = tmp + 1;
  
  struct Node* parent = node->parent;
  if(parent==0){
    //@ close Node(node, parent, left, right, count + 1);
  } else {
    //@ close Node(node, parent, left, right, count + 1);
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
//@ requires Node(n, ?parent, ?left, ?right, ?count);
//@ ensures Node(n, parent, left, right, count) &*& result == count;
{
  //@ open Node(n, parent, left, right, count);
  int c = n->count;
  //@ close Node(n, parent, left, right, count);
  return c;
}