/*@ predicate tree(struct Node* n; int c) =
  n != 0 ?
    malloc_block_Node(n) &*&
    tree(n->left, ?c1) &*&
    tree(n->right, ?c2) &*&
    c == 1 + c1 + c2 &*&
    (n->left != 0 ==> n->left->parent == n) &*&
    (n->right != 0 ==> n->right->parent == n)
  :
    c == 0;
@*/

/*@ predicate root(struct Node* n) =
  tree(n, ?c) &*& n->parent == 0;
@*/

//@ requires true;
//@ ensures root(result);
struct Node* create();

//@ requires root(node);
//@ ensures root(node) &*& tree(result, 1);
struct Node* addLeft(struct Node* node);

//@ requires tree(n, c);
//@ ensures result == c;
int getNbOfNodes(struct Node* n);

struct Node {
  struct Node* left;
  struct Node* right;
  struct Node* parent;
  int count;
};

//@ requires parent == 0 ? true : root(parent);
//@ ensures tree(result, 1) &*& (parent != 0 ==> parent->left == result || parent->right == result);
struct Node* internalCreate(struct Node* parent);

//@ requires root(node);
//@ ensures root(node) &*& tree(result, 1);
struct Node* internalAddLeft(struct Node* node);

//@ requires tree(node, ?c) &*& c < INT_MAX;
//@ ensures tree(node, c + 1) &*& (node->parent != 0 ==> tree(node->parent, ?cp));
void fix(struct Node* node);

//@ requires true;
//@ ensures false;
void abort();

//@ requires tree(n, c);
//@ ensures result == c;
int internalGetNbOfNodes(struct Node* n);

int main() 
{
  struct Node* mytree = create();
  struct Node* child = addLeft(mytree);
  
  struct Node* child2 = addLeft(child);
  
  int c = getNbOfNodes(child2);
  //@ assert c == 1;
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