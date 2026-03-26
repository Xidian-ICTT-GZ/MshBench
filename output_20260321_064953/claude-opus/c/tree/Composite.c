struct Node {
  struct Node* left;
  struct Node* right;
  struct Node* parent;
  int count;
};

/*@
predicate nodes(struct Node* n) =
  n == 0 ?
    emp
  :
    malloc_block_Node(n) &*&
    nodes(n->left) &*& nodes(n->right) &*&
    n->parent |-> ?p &*& n->left |-> ?l &*& n->right |-> ?r &*& n->count |-> _;
@*/

struct Node* create() 
  //@ requires true;
  //@ ensures nodes(result);
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

struct Node* internalCreate(struct Node* parent)
  //@ requires true;
  //@ ensures nodes(result);
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
  //@ requires nodes(node);
  //@ ensures nodes(node);
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

struct Node* internalAddLeft(struct Node* node)
  //@ requires nodes(node);
  //@ ensures nodes(node) &*& nodes(result);
{
    struct Node* child = internalCreate(node);
    node->left = child;
    fix(node);
    return child;
}

struct Node* addLeft(struct Node* node)
  //@ requires nodes(node);
  //@ ensures nodes(node) &*& nodes(result);
{
  struct Node* newChild = internalAddLeft(node);
  return newChild;
}

int internalGetNbOfNodes(struct Node* n)
  //@ requires nodes(n);
  //@ ensures nodes(n) &*& result == n->count;
{
  int c = n->count;
  return c;
}

int getNbOfNodes(struct Node* n)
  //@ requires nodes(n);
  //@ ensures nodes(n);
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

void abort()
  //@ requires true;
  //@ ensures false;
{
  while(true)
  {
  }
}